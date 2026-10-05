"""Re-express experiment 048's 72 registered cases; no new scenarios.

Losses are divided by initial wealth. Re-solve only the original dynamic
programs to recover statewise holdings omitted from their saved summaries,
then compute actual expected trading expenditure for all three policies.
The original summaries and experiment code are never modified.
"""
from pathlib import Path
import csv
import hashlib
import importlib.util
import json
import platform
from importlib.metadata import version
import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
spec = importlib.util.spec_from_file_location('comparison048', ROOT/'experiments/048/run.py')
E = importlib.util.module_from_spec(spec)
spec.loader.exec_module(E)
source = ROOT/'experiments/048/summary.json'
cells = json.loads(source.read_text())['cells']
rows = []
max_error = 0.0
for index, c in enumerate(cells):
    M = E.model(c['regime'], c['unc'], c['costmul'])
    start = np.asarray(c['start']); wealth = float(start.sum()+c['cash'])
    D = M.solve(start, c['cash'], T=2)
    nodes = D['levels'][1]
    err = abs(D['value']-c['dynamic']['value'])
    max_error = max(max_error, err)
    assert err < 2e-8, (index, err)
    row = {k:c[k] for k in ['regime','start','cash','unc','costmul','fund_rate','etf_rate']}
    row.update(index=index, initial_wealth=wealth, myopic_exact=c['myopic_optimal'], binding=c['dynamic']['binds'])
    for policy in ['dynamic','myopic','ef111']:
        p = c[policy]
        x0 = np.asarray(p['x0']) if policy!='dynamic' else np.asarray(D['x'][0][0])
        x1 = p['x1'] if policy!='dynamic' else D['x'][1]
        mu0,S0=M.moments(0,M.m0)
        score_check=E.score(M,mu0,S0,x0,start)
        for nd,x in zip(nodes,x1):
            mu1,S1=M.moments(1,nd['m'])
            score_check+=M.beta*nd['prob']*E.score(M,mu1,S1,np.asarray(x),x0*nd['g'])
        assert abs(score_check-p['value'])<2e-8, (index,policy,score_check,p['value'])
        C0 = E.cost(M, x0-start)
        C1 = sum(nd['prob']*E.cost(M, np.asarray(x)-x0*nd['g']) for nd,x in zip(nodes,x1))
        row[policy] = dict(x0=x0.tolist(), x1=[np.asarray(x).tolist() for x in x1],
            loss_wealth_bp=1e4*(c['dynamic']['value']-p['value'])/wealth,
            cost_today_wealth_bp=1e4*C0/wealth,
            cost_tomorrow_wealth_bp=1e4*C1/wealth,
            cost_total_wealth_bp=1e4*(C0+M.beta*C1)/wealth)
    rows.append(row)
    if (index+1)%12==0: print(f'Reproduced {index+1}/72',flush=True)
out = dict(description=__doc__, source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    environment={'python':platform.python_version(), **{n:version(n) for n in ['numpy','cvxpy','clarabel']}},
    input_hashes={str(p):hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in map(Path, ['uv.lock','experiments/048/run.py','experiments/047/run.py','experiments/d16-harness/harness.py','experiments/presets.py'])},
    max_dynamic_objective_reproduction_error=max_error, cells=rows)
(HERE/'figures/policy_analysis.json').write_text(json.dumps(out,indent=2)+'\n')
flat=[]
for r in rows:
    for policy in ['dynamic','myopic','ef111']:
        p=r[policy]
        flat.append({k:r[k] for k in ['index','regime','start','cash','unc','costmul','initial_wealth','myopic_exact','binding']}|
                    {'policy':policy}|{k:v for k,v in p.items() if k not in ['x0','x1']})
with (HERE/'figures/policy_analysis.csv').open('w') as f:
    w=csv.DictWriter(f,fieldnames=flat[0].keys());w.writeheader();w.writerows(flat)
print('Maximum dynamic objective reproduction error:',max_error)
for policy in ['myopic','ef111']:
    r=max(rows,key=lambda r:r[policy]['loss_wealth_bp'])
    print(policy,'maximum-loss case:',r['index'])
    print({p:{k:v for k,v in r[p].items() if k not in ['x0','x1']} for p in ['dynamic','myopic','ef111']})
