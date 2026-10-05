"""Stage 1, run before the dynamic analysis: economic diversification and independent check."""
import itertools,json
import numpy as np
from scipy.optimize import minimize
import menu as S

def solution(M,etfs_only=False):
    mu,V=M.moments(0,M.m0)
    if etfs_only:
        old=M.cap.copy();M.cap[:6]=0
    x,_,h=M.one_review(mu,V,np.zeros(9),1.)
    if etfs_only:M.cap=old
    return dict(x=x.tolist(),cash=h,sleeves=S.sleeves(x).tolist(),
                mean_bp=float(mu@x*1e4),sd_pct=float(np.sqrt(x@V@x)*100),
                score_bp=float((mu@x-M.gamma/2*x@V@x-M.cost(x))*1e4),
                max_weight=float(max(x)),positions_above_1pct=int(sum(x>.01)))

def main():
    # Direct economic covariance and a separately written optimizer.
    sig=np.array([.08,.03,.04]);corr=np.array([[1,0,.4],[0,1,.2],[.4,.2,1]])
    cov=np.diag(sig)@corr@np.diag(sig)
    assert np.max(abs(S.BE@np.diag(S.SF**2)@S.BE.T-cov))<1e-12
    assert np.max(abs(S.BE@S.LAM-np.array([.012,.003,.006])))<1e-12
    records=[]
    for gamma,alpha_scale,uncertainty in itertools.product((2.,2.5,3.),(0.,1.,2.),(.5,1.,2.)):
        M=S.build(gamma=gamma,alpha_scale=alpha_scale,uncertainty=uncertainty,fund_bp=0,etf_bp=0)
        mu,V=M.moments(0,M.m0);full=solution(M);etfs=solution(M,True)
        # Exact one-dimensional constrained quadratic for each instrument plus cash.
        w=np.clip(mu/(gamma*np.diag(V)),0,1)
        scores=mu*w-gamma/2*np.diag(V)*w*w;j=int(np.argmax(scores))
        one=dict(instrument=S.NAMES[j],weight=float(w[j]),cash=float(1-w[j]),score_bp=float(scores[j]*1e4))
        records.append(dict(gamma=gamma,alpha_scale=alpha_scale,uncertainty=uncertainty,full=full,etfs=etfs,
                            best_single=one,diversification_gain_bp=full["score_bp"]-one["score_bp"]))
    base=next(r for r in records if r["gamma"]==2.5 and r["alpha_scale"]==r["uncertainty"]==1)
    M=S.build(fund_bp=0,etf_bp=0);mu,V=M.moments(0,M.m0)
    # Independent moment construction in sleeve coordinates, including prior uncertainty and residual risk.
    B=np.vstack([S.Q,np.eye(3)])
    Vs=cov+S.BE@np.diag(S.PL_SD**2)@S.BE.T
    Vind=B@Vs@B.T+np.diag(np.r_[S.SA**2+S.PA_SD**2,S.SE**2])
    mind=B@np.array([.012,.003,.006])+np.r_[S.ALPHA,-S.FEE]
    assert np.max(abs(V-Vind))<1e-12 and np.max(abs(mu-mind))<1e-12
    opt=minimize(lambda x:1e4*(2.5/2*x@Vind@x-mind@x),np.ones(9)/9,
                 jac=lambda x:1e4*(2.5*Vind@x-mind),bounds=[(0,1)]*9,
                 constraints={"type":"ineq","fun":lambda x:1-x.sum(),"jac":lambda x:-np.ones(9)},
                 method="SLSQP",options={"ftol":1e-11,"maxiter":1000})
    assert opt.success,opt.message
    err=float(np.max(abs(opt.x-np.array(base["full"]["x"]))))
    assert err<1e-5,err
    with_costs=solution(S.build())
    out=dict(results=records,baseline=base,baseline_with_costs=with_costs,
             independent_max_holding_difference=err,sleeve_covariance=cov.tolist(),
             names=S.NAMES)
    (S.HERE/"static_results.json").write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps(dict(baseline=base,baseline_with_costs=with_costs,independent_error=err,
                         min_gain=min(r['diversification_gain_bp'] for r in records),
                         max_concentration=max(r['full']['max_weight'] for r in records)),indent=2))

if __name__=="__main__":main()
