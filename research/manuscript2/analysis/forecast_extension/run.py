"""Apply the existing funded M9 solvers to old-optimal starting holdings."""
import csv
import hashlib
import json
import multiprocessing as mp
import platform
import sys
import time
import warnings
import numpy as np
from scipy.optimize import minimize
import extension_inputs as S
sys.path.insert(0, str(S.ROOT / 'experiments/d26-prep'))
import policies as P
from harness_n import OPT

def old_portfolio(c):
    M = S.build(c, old=True, free=True)
    mu, V = M.moments(0, M.m0)
    x, _, h = M.one_review(mu, V, np.zeros(9), 1.)
    # Remove solver-scale negative residual cash/holdings before using as an incumbent.
    x = np.maximum(x, 0)
    if x.sum() > 1:
        x /= x.sum()
    h = 1 - x.sum()
    # Independently construct predictive moments in sleeve coordinates.
    D = S.D; B = np.vstack([D.Q, np.eye(3)])
    vol = np.array([.08, .03, .04])
    corr = np.array([[1, 0, .4], [0, 1, .2], [.4, .2, 1]])
    vc = np.diag(vol) @ corr @ np.diag(vol)
    vc += D.BE @ np.diag((D.PL_SD*c['uncertainty'])**2) @ D.BE.T
    vi = B @ vc @ B.T + np.diag(np.r_[D.SA**2+(D.PA_SD*c['uncertainty'])**2, D.SE**2])
    mi = B @ np.array([.012, .003, .006]) + np.r_[D.ALPHA+c['alpha_offset_bp']/1e4, -D.FEE]
    if c['menu']=='unspanned':
        vv=np.r_[S.STYLE,np.zeros(3)]
        vi+=np.outer(vv,vv)*(.03**2+(c['style_prior_bp']/1e4)**2)
    assert max(np.max(abs(mi-mu)), np.max(abs(vi-V))) < 1e-12
    opt = minimize(lambda y: 1e4*(c['gamma']/2*y@vi@y-mi@y), np.ones(9)/9,
                   jac=lambda y: 1e4*(c['gamma']*vi@y-mi), bounds=[(0, 1)]*9,
                   constraints={'type':'ineq', 'fun':lambda y: 1-y.sum(), 'jac':lambda y:-np.ones(9)},
                   method='SLSQP', options={'ftol':1e-9, 'maxiter':1000})
    assert opt.success, opt.message
    err = np.max(abs(opt.x-x)); assert err < 1e-5, err
    actual = S.build(c, old=True)
    xc, _, _ = actual.one_review(mu, V, x, h)
    control_trade = np.max(abs(xc-x)); assert control_trade < 1e-5, control_trade
    return x, float(h), float(err), float(control_trade)

def evaluate(c):
    began = time.monotonic()
    with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter('always')
        xm, hm, static_error, nochange = old_portfolio(c)
        M = S.build(c); mu, V = M.moments(0, M.m0)
        D = M.solve(xm, hm)
        attempts=[D['status']]
        if D['status'] != 'optimal':
            saved=OPT.copy()
            try:
                OPT.update(tol_gap_abs=1e-10,tol_gap_rel=1e-10,tol_feas=1e-10,max_iter=1000)
                D=M.solve(xm,hm);attempts.append(D['status'])
            finally:
                OPT.clear();OPT.update(saved)
        if D['status'] != 'optimal':
            saved=OPT.copy()
            try:
                OPT.update(tol_gap_abs=1e-8,tol_gap_rel=1e-9,tol_feas=1e-9,max_iter=1000)
                D=M.solve(xm,hm);attempts.append(D['status'])
            finally:
                OPT.clear();OPT.update(saved)
        assert D['status'] == 'optimal', (c,D['status'])
        nodes = D['levels'][1]; q = np.array([n['prob'] for n in nodes])
        assert min(n['g'].min() for n in nodes) > 0
        my, _, hmy = M.one_review(mu, V, xm, hm)
        etf, _, hetf = M.one_review(mu, V, xm, hm, frozen=tuple(range(6)))
        assert max(abs(etf[:6]-xm[:6])) < 2e-7
        out = {}
        for name, x in [('myopic', my), ('dynamic', D['x'][0][0]), ('etf_only', etf)]:
            h = P.cash_after(M, hm, x, xm)
            if name == 'dynamic':
                tm = []
                for k, nd in enumerate(nodes):
                    xx = D['x'][1][k]; carried = nd['g']*x
                    mm, vv = M.moments(1, nd['m'])
                    hh = P.cash_after(M, h, xx, carried)
                    tm.append(dict(x1=xx, xm=carried, h=hh, score=P.score(M, mm, vv, xx, carried)))
                    assert abs(hh-D['h'][1][k]) < 2e-7
            else:
                tm = P.tomorrow(M, nodes, x, h)
            c0 = P.cost(M, x-xm)
            assert abs(x.sum()+h+c0-1) < 1e-9
            assert min(x.min(), h, min(t['x1'].min() for t in tm), min(t['h'] for t in tm)) > -2e-7
            budgeterr = max(abs(t['x1'].sum()+t['h']+P.cost(M, t['x1']-t['xm'])-t['xm'].sum()-h) for t in tm)
            assert budgeterr < 2e-7
            s0 = P.score(M, mu, V, x, xm)*1e4
            s1 = float(q @ [t['score'] for t in tm])*1e4
            out[name] = dict(x=x.tolist(), trade=(x-xm).tolist(), cash=float(h),
                             etfs_pct=float(100*x[6:].sum()), funds_pct=float(100*x[:6].sum()),
                             gross_trade_pct=float(100*np.abs(x-xm).sum()),
                             gross_fund_trade_pct=float(100*np.abs(x[:6]-xm[:6]).sum()),
                             cost0_bp=c0*1e4, score0_bp=s0, continuation_bp=s1, value_bp=s0+s1,
                             sleeve_exposures=S.D.sleeves(x).tolist(),
                             factor_exposures=(np.vstack([M.BA,M.BE]).T@x).tolist(),
                             expected_next_trade=(q @ np.array([t['x1']-t['xm'] for t in tm])).tolist(),
                             expected_cost1_bp=float(q @ [P.cost(M, t['x1']-t['xm']) for t in tm])*1e4,
                             future_min_cash=float(min(t['h'] for t in tm)), budget_error=float(budgeterr))
        objerr = out['dynamic']['value_bp']/1e4-D['value']
        assert abs(objerr) < 1e-8, objerr
        gain = out['dynamic']['value_bp']-out['myopic']['value_bp']
        assert gain > -1e-4, gain
        assert out['myopic']['score0_bp'] >= out['etf_only']['score0_bp']-1e-5
        return dict(**c, initial_x=xm.tolist(), initial_cash=hm, initial_factor_exposures=(np.vstack([M.BA,M.BE]).T@xm).tolist(), static_error=static_error,
                    old_beliefs_max_trade=nochange, **out, gain_bp=gain,
                    current_fund_permission_gain_bp=out['myopic']['score0_bp']-out['etf_only']['score0_bp'],
                    status=D['status'], joint_attempts=attempts, states=len(nodes), objective_error=objerr,
                    warnings=[str(w.message) for w in caught], seconds=time.monotonic()-began)

def main():
    assert (S.HERE / 'DESIGN.md').exists()
    done = []; began = time.monotonic()
    with (S.HERE / 'cases.jsonl').open('w') as f, mp.get_context('spawn').Pool(4) as pool:
        for r in pool.imap_unordered(evaluate, S.cases()):
            done.append(r); f.write(json.dumps(r)+'\n'); f.flush()
            if len(done)%9 == 0:
                print(f"{len(done)}/49; {time.monotonic()-began:.1f}s; gain {r['gain_bp']:.6f} bp", flush=True)
    done.sort(key=lambda r:r['case_id'])
    import cvxpy, clarabel
    paths = [S.HERE / f for f in ('DESIGN.md', 'extension_inputs.py', 'run.py')]
    paths += [S.HERE.parent/'diversified/menu.py', S.ROOT/'experiments/d16-harness/harness_n.py',
              S.ROOT/'experiments/d26-prep/policies.py', S.ROOT/'uv.lock']
    output = dict(results=done, wall_seconds=time.monotonic()-began,
                  environment=dict(python=platform.python_version(), platform=platform.platform(),
                                   numpy=np.__version__, cvxpy=cvxpy.__version__, clarabel=clarabel.__version__),
                  source_hashes={str(p.relative_to(S.ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths})
    (S.HERE/'results.json').write_text(json.dumps(output, indent=2)+'\n')
    rows = []
    for r in done:
        row = {k:v for k,v in r.items() if not isinstance(v, (dict,list))}
        row['warning_count'] = len(r['warnings'])
        for p in ('myopic','dynamic','etf_only'):
            row.update({p+'_'+k:v for k,v in r[p].items() if not isinstance(v,list)})
        rows.append(row)
    with (S.HERE/'results.csv').open('w', newline='') as f:
        w=csv.DictWriter(f, fieldnames=rows[0].keys()); w.writeheader(); w.writerows(rows)
    print('Completed; funding, objective and old-portfolio checks passed.', flush=True)

if __name__ == '__main__':
    main()
