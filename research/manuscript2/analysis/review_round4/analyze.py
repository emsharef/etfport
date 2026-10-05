"""Round-four diagnostics from existing cases; no economic inputs are changed."""
from pathlib import Path
import csv, hashlib, importlib.util, json, sys, warnings
import numpy as np
import cvxpy as cp
HERE=Path(__file__).resolve().parent
PREV=HERE.parent/'forecast_revision'
sys.path.insert(0,str(PREV))
spec=importlib.util.spec_from_file_location('round4_reference',PREV/'verify.py')
V=importlib.util.module_from_spec(spec);spec.loader.exec_module(V)
NAMES=V.S.NAMES
OPT=dict(solver='CLARABEL',tol_gap_abs=1e-10,tol_gap_rel=1e-10,tol_feas=1e-11,max_iter=1000)

def diagnostics(I, fixed=None):
    n,z=I['g'].shape
    x=cp.Variable(n);u=cp.Variable(n,nonneg=True);v=cp.Variable(n,nonneg=True)
    c=I['rates']@(u+v);h=I['hm']-cp.sum(x-I['xm'])-c
    X=cp.Variable((n,z));U=cp.Variable((n,z),nonneg=True);W=cp.Variable((n,z),nonneg=True)
    carried=cp.multiply(I['g'],cp.reshape(x,(n,1),order='F'));C=I['rates']@(U+W)
    H=h-cp.sum(X-carried,axis=0)-C
    cons=[x>=0,x-I['xm']==u-v,h>=0,X>=0,X-carried==U-W,H>=0]
    if fixed is not None:cons.append(x==fixed)
    current=I['mu0']@x-1.25*cp.quad_form(x,cp.psd_wrap(I['V0']))-c
    later=(cp.sum(cp.multiply(I['mu1'],X))-1.25*cp.sum_squares(np.linalg.cholesky(I['V1']).T@X)-cp.sum(C))/z
    prob=cp.Problem(cp.Maximize(1e4*(current+later)),cons)
    prob.solve(**OPT);assert prob.status=='optimal',prob.status
    eta0=float(cons[2].dual_value)/1e4
    eta1=np.asarray(cons[5].dual_value)*z/1e4
    result=dict(x=x.value.tolist(),value_bp=float(prob.value),root_cash=float(h.value),
      next_cash_min=float(np.min(H.value)),next_cash_max=float(np.max(H.value)),
      conditional_eta1=eta1.tolist(),eta1_min=float(eta1.min()),eta1_mean=float(eta1.mean()),eta1_max=float(eta1.max()),
      probability_eta1_positive=float(np.mean(eta1>1e-7)),max_future_complementarity=float(np.max(abs(eta1*H.value))))
    if fixed is None:result.update(eta0=eta0,effective_eta0=eta0+float(eta1.mean()))
    return result

def one(I):
    x=cp.Variable(9);u=cp.Variable(9,nonneg=True);v=cp.Variable(9,nonneg=True)
    c=I['rates']@(u+v);h=I['hm']-cp.sum(x-I['xm'])-c
    cons=[x>=0,x-I['xm']==u-v,h>=0]
    prob=cp.Problem(cp.Maximize(1e4*(I['mu0']@x-1.25*cp.quad_form(x,cp.psd_wrap(I['V0']))-c)),cons)
    prob.solve(**OPT);assert prob.status=='optimal'
    return x.value,float(cons[2].dual_value)/1e4,float(h.value)

def main():
    paths=[PREV/'results.json',HERE.parent/'forecast_extension/results.json']
    grids=[json.loads(p.read_text())['results'] for p in paths]
    base={r['scenario']:r for r in grids[0] if V.S.baseline(r)}
    rows=[];trades=[]
    for source,rr in zip(('revisions','extension'),grids):
      for r in rr:
        assert abs(r['gain_bp']-(r['dynamic']['value_bp']-r['myopic']['value_bp']))<1e-8
        assert abs(r['current_fund_permission_gain_bp']-(r['myopic']['score0_bp']-r['etf_only']['score0_bp']))<1e-8
        row=dict(source=source,case_id=r['case_id'],scenario=r['scenario'],menu=r.get('menu','spanned'),
          revision_bp=r.get('revision_bp',''),persistence=r.get('persistence',''),style_prior_bp=r.get('style_prior_bp',''),
          gamma=r['gamma'],alpha_offset_bp=r.get('alpha_offset_bp',0),uncertainty=r.get('uncertainty',1),fund_bp=r['fund_bp'],etf_bp=r['etf_bp'],
          current_fund_benefit_bp=r['current_fund_permission_gain_bp'],planning_gain_bp=r['gain_bp'])
        for pol in ('etf_only','myopic','dynamic'):
          v=r[pol];row[pol+'_current_cost_bp']=v['cost0_bp'];row[pol+'_expected_next_cost_bp']=v['expected_cost1_bp']
          for j,n in enumerate(NAMES):
            trades.append(dict(source=source,case_id=r['case_id'],scenario=r['scenario'],policy=pol,instrument=n,
              initial_holding_pct=100*r['initial_x'][j],current_trade_pct=100*v['trade'][j],posttrade_holding_pct=100*v['x'][j],
              expected_next_trade_pct=100*v['expected_next_trade'][j],current_cash_pct=100*v['cash'],current_cost_bp=v['cost0_bp']))
        rows.append(row)
    for name,rr in [('case_metrics.csv',rows),('instrument_trades.csv',trades)]:
      with (HERE/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rr[0].keys());w.writeheader();w.writerows(rr)
    summary={label:dict(cases=len(rr),median_planning_gain_bp=float(np.median([r['gain_bp'] for r in rr])),max_planning_gain_bp=max(r['gain_bp'] for r in rr),max_current_fund_benefit_bp=max(r['current_fund_permission_gain_bp'] for r in rr)) for label,rr in zip(('revisions','extension'),grids)}
    summary['fee_credit_bp']=(V.S.D.Q@V.S.D.FEE*1e4).tolist()
    summary['negative_alpha']=[dict(scenario=r['scenario'],initial_funds_pct=100*sum(r['initial_x'][:6]),initial_x=r['initial_x'],
      **{pol:dict(fund_gross_trade_pct=r[pol]['gross_fund_trade_pct'],trade=r[pol]['trade']) for pol in ('myopic','dynamic')},
      gain_bp=r['gain_bp'],current_fund_benefit_bp=r['current_fund_permission_gain_bp']) for r in grids[0] if r['alpha_offset_bp']==-5]
    checks=[]
    for scenario in ('premium_down_persistent','alpha_up','alpha_down'):
      with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter('always')
        I=V.data(scenario);x,eta,h=one(I);dyn=diagnostics(I);my=diagnostics(I,x)
      r=base[scenario]
      err=max(float(np.max(abs(x-r['myopic']['x']))),float(np.max(abs(np.array(dyn['x'])-r['dynamic']['x']))))
      valerr=max(abs(dyn['value_bp']-r['dynamic']['value_bp']),abs(my['value_bp']-r['myopic']['value_bp']))
      assert err<1e-5 and valerr<1e-5,(err,valerr)
      checks.append(dict(scenario=scenario,myopic_root_eta=eta,myopic_root_cash=h,dynamic=dyn,myopic_continuation=my,
        max_holding_error=err,max_value_error_bp=valerr,warnings=[str(w.message) for w in caught]))
      print(scenario,'eta0',dyn['eta0'],'Eeta1',dyn['eta1_mean'],'min/max',dyn['eta1_min'],dyn['eta1_max'],'prob',dyn['probability_eta1_positive'],flush=True)
    summary['duals']=checks
    summary['source_hashes']={str(p.relative_to(HERE.parents[2])):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths+[Path(__file__),HERE/'DESIGN.md',PREV/'verify.py',PREV/'inputs.py',HERE.parent/'diversified/menu.py']}
    summary['cvxpy']=cp.__version__;summary['numpy']=np.__version__;summary['solver_settings']=OPT
    (HERE/'diagnostics.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k in ('revisions','extension','fee_credit_bp')},indent=2))
if __name__=='__main__':main()
