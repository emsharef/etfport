"""Diagnostics requested in review round 2; existing 72-case design only.

Design, fixed before running this script:
* Find the feasible fund interval at the exposure-first policy's chosen
  exposure at every visited date/state by intersecting its piecewise-linear
  cash inequality with the position bounds. Report widths <= 1e-6 initial
  wealth as near-singleton, with 1e-7 and 1e-5 sensitivity counts.
* Attribute losses only via the one-date Bellman gap at each policy's OWN
  state; report how much of the second-date loss occurs at near-singletons.
  A near-singleton classification alone does not establish causation.
* For Figure 3B, compute exposure change needed to admit today's joint
  one-date optimum. This is not a backtest of a tolerance-based policy.
* For Figure 3A, tabulate ETF trade directions and the marked continuation
  marginal from the already saved future holdings. No new parameter cells.
"""
from pathlib import Path
import importlib.util,json,hashlib,csv,warnings
import numpy as np
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('E48',ROOT/'experiments/048/run.py');E=importlib.util.module_from_spec(spec);spec.loader.exec_module(E)
source=ROOT/'experiments/048/summary.json';cells=json.loads(source.read_text())['cells']
analysis=HERE/'figures/policy_analysis.json';saved=json.loads(analysis.read_text())['cells']

def interval(M,xm,hm,w):
    hi=max(0,min(M.capA,w))
    xs=sorted(set([0.,hi]+[float(v) for v in [xm[0],w-xm[1]] if 0<v<hi]))
    ys=np.array([E.cost(M,np.array([x,w-x])-xm) for x in xs])
    budget=hm+sum(xm)-w
    assert min(ys)-budget<1e-8, (min(ys),budget)
    # Repair only a solver-rounding infeasibility; never enlarge positive slack.
    budget=max(budget,float(min(ys)))
    good=[x for x,y in zip(xs,ys) if y<=budget]
    for a,b,ya,yb in zip(xs[:-1],xs[1:],ys[:-1],ys[1:]):
        if (ya-budget)*(yb-budget)<0:
            good.append(a+(b-a)*(budget-ya)/(yb-ya))
    assert good
    return float(min(good)),float(max(good))

def halfspace_interval(M,xm,hm,w):
    # Independent check: a sum of two absolute values is the maximum of
    # four affine functions. Each one must fit inside the cash budget.
    assert M.kAp == M.kAm and M.kEp == M.kEm
    lo,hi=0.,min(M.capA,w)
    budget=hm+sum(xm)-w
    for sa in [-1,1]:
        for se in [-1,1]:
            slope=M.kAp*sa-M.kEp*se
            rhs=budget+M.kAp*sa*xm[0]-M.kEp*se*(w-xm[1])
            if slope>0: hi=min(hi,rhs/slope)
            elif slope<0: lo=max(lo,rhs/slope)
            else: assert rhs>=-1e-8
    return lo,hi

records=[];node_records=[];solver_warnings=[]
for index,c in enumerate(cells):
    M=E.model(c['regime'],c['unc'],c['costmul']);nodes=M.tree(2)[1]
    start=np.array(c['start']);W0=sum(start)+c['cash'];p=c['ef111'];x0=np.array(p['x0'])
    bounds=interval(M,start,c['cash'],sum(x0))
    independent=halfspace_interval(M,start,c['cash'],sum(x0))
    assert np.max(np.abs(np.array(bounds)-independent))/W0<1e-7
    mu,S=M.moments(0,M.m0)
    local_gap0=E.score(M,mu,S,np.array(c['myopic']['x0']),start)-E.score(M,mu,S,x0,start)
    rec=dict(index=index,regime=c['regime'],start=c['start'],cash=c['cash'],unc=c['unc'],costmul=c['costmul'],initial_wealth=W0,
             root_width_wealth=(bounds[1]-bounds[0])/W0,root_joint_loss_wealth_bp=1e4*local_gap0/W0,
             dynamic_loss_wealth_bp=1e4*(c['dynamic']['value']-p['value'])/W0)
    future=[]
    for j,(nd,x) in enumerate(zip(nodes,p['x1'])):
        x=np.array(x);xm=x0*nd['g'];hm=max(0,p['h0p']);bounds=interval(M,xm,hm,sum(x));mu,S=M.moments(1,nd['m'])
        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter('always')
            best=E.one(M,mu,S,xm,hm)[0]
        solver_warnings.extend(dict(index=index,node=j,message=str(v.message)) for v in caught)
        gap=E.score(M,mu,S,best,xm)-E.score(M,mu,S,x,xm)
        assert gap>-2e-8
        future.append(dict(index=index,node=j,prob=nd['prob'],width_wealth=(bounds[1]-bounds[0])/W0,
                           local_loss_wealth_bp=1e4*gap/W0))
    for eps in [1e-7,1e-6,1e-5]:
        key=f'{eps:.0e}'
        rec['future_near_prob_'+key]=sum(n['prob'] for n in future if n['width_wealth']<=eps)
        rec['future_near_loss_'+key]=sum(n['prob']*n['local_loss_wealth_bp'] for n in future if n['width_wealth']<=eps)
    rec['future_total_local_loss']=sum(n['prob']*n['local_loss_wealth_bp'] for n in future)
    records.append(rec);node_records.extend(future)

summary={}
for eps in [1e-7,1e-6,1e-5]:
    key=f'{eps:.0e}'
    summary[key]=dict(root_near_cells=sum(r['root_width_wealth']<=eps for r in records),
      root_near_and_local_loss_above_001bp=sum(r['root_width_wealth']<=eps and r['root_joint_loss_wealth_bp']>.01 for r in records),
      any_date_near_cells=sum(r['root_width_wealth']<=eps or r['future_near_prob_'+key]>0 for r in records),
      any_date_near_and_local_loss_above_001bp=sum((r['root_width_wealth']<=eps and r['root_joint_loss_wealth_bp']>.01) or r['future_near_loss_'+key]>.01 for r in records),
      root_near_max_dynamic_loss_bp=max(r['dynamic_loss_wealth_bp'] for r in records if r['root_width_wealth']<=eps),
      no_date_near_max_dynamic_loss_bp=max(r['dynamic_loss_wealth_bp'] for r in records if r['root_width_wealth']>eps and r['future_near_prob_'+key]==0))
# Threshold diagnostics describe visited states, not an intervention removing degeneracy.
b=21;c=cells[b];r=records[b];wef=sum(c['ef111']['x0']);wj=sum(c['myopic']['x0'])
figB=dict(case_index=b,first_stage_exposure=wef,joint_exposure=wj,
          required_tolerance_wealth_bp=1e4*abs(wef-wj)/r['initial_wealth'],root_width_wealth=r['root_width_wealth'],
          root_joint_loss_wealth_bp=r['root_joint_loss_wealth_bp'],
          future_local_loss_wealth_bp=r['future_total_local_loss'])
figA={'case_index':45}
c=cells[45];M=E.model(c['regime'],c['unc'],c['costmul']);nodes=M.tree(2)[1]
for kind in ['dynamic','myopic']:
    p=saved[45][kind];x0=np.array(p['x0']);x1=np.array(p['x1']);g=np.array([n['g'] for n in nodes]);q=np.array([n['prob'] for n in nodes]);u=x1-g*x0
    slopes=[]
    for nd,x,v in zip(nodes,x1,u):
        mu,S=M.moments(1,nd['m']);slopes.append(M.kEp if v[1]>1e-7 else -M.kEm if v[1]<-1e-7 else float((mu-M.gamma*S@x)[1]))
    SE=float(q@(g[:,1]*slopes));mu0,S0=M.moments(0,M.m0)
    figA[kind]=dict(etf_sell_probability=float(q[u[:,1]<-1e-7].sum()),etf_buy_probability=float(q[u[:,1]>1e-7].sum()),
        fund_at_cap_probability=float(q[x1[:,0]>=M.capA-1e-7].sum()),expected_etf_holding=float(q@x1[:,1]),
        expected_etf_trade=float(q@u[:,1]),S_E=SE,root_etf_marginal=float((mu0-M.gamma*S0@x0)[1]),
        expected_tomorrow_cash_multiplier=float(q@c[kind]['eta1']))
assert abs(figA['dynamic']['root_etf_marginal']+figA['dynamic']['S_E']+M.kEm)<1e-7
out=dict(design=__doc__,inputs={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [source,analysis,Path(__file__).resolve()]},
         summary=summary,figure3A=figA,figure3B=figB,cells=records,nodes=node_records,
         checks={'independent_root_interval_check':'All 72 agree within 1e-7 initial wealth using four affine cash inequalities.'},
         solver_warnings=solver_warnings)
(HERE/'figures/round2_diagnostics.json').write_text(json.dumps(out,indent=2,default=lambda o:o.item())+'\n')
with (HERE/'figures/round2_diagnostics.csv').open('w') as f:
    wr=csv.DictWriter(f,fieldnames=records[0]);wr.writeheader();wr.writerows(records)
print(json.dumps({k:out[k] for k in ['summary','figure3A','figure3B']},indent=2,default=lambda o:o.item()))
