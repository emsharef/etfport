"""Independent baseline checks: direct tree/filter and vectorized CVXPY QPs.

No lab moment, tree, policy or optimization routine is used. Nine cases,
including the unchanged-beliefs control. Input constants alone are shared.
"""
import json
import warnings
import cvxpy as cp
import numpy as np
from scipy.optimize import minimize
import inputs as S

OPT = dict(solver='CLARABEL', tol_gap_abs=1e-11, tol_gap_rel=1e-11, tol_feas=1e-11, max_iter=1000)

def axes(sd):
    return [sign*np.sqrt(len(sd))*np.eye(len(sd))[i]*sd[i]
            for i in range(len(sd)) for sign in (-1, 1)]

def data(scenario):
    D=S.D
    old=np.r_[D.LAM,D.ALPHA]; current=old.copy(); future=old.copy()
    # Specify the expected next-review means directly, independently of theta_bar construction.
    if scenario.startswith('premium_') or scenario.startswith('anticipated_'):
        direction = -1 if '_up' in scenario else 1
        change = np.linalg.inv(D.BE) @ (direction*np.array([-.0015,.0005,0]))
        if scenario.startswith('anticipated_'):
            future[:3] += change
        else:
            current[:3] += change
            future[:3] += change*(.8 if scenario.endswith('reverting') else 1.)
    elif scenario in ('alpha_up','alpha_down'):
        current[3] += .0005 if scenario == 'alpha_up' else -.0005
        future=current.copy()
    else:
        assert scenario == 'unchanged'
    p0=np.r_[D.PL_SD,D.PA_SD]**2
    K=p0/(p0+np.r_[D.SF,D.SA]**2)
    p1=.64*(1-K)*p0+D.STATE_SD**2
    B=np.vstack([D.BA,D.BE]); G=np.block([[D.BA,np.eye(6)],[D.BE,np.zeros((3,6))]])
    fee=np.r_[np.zeros(6),-D.FEE]
    Vr=B@np.diag(D.SF**2)@B.T+np.diag(np.r_[D.SA**2,D.SE**2])
    V0=Vr+G@np.diag(p0)@G.T; V1=Vr+G@np.diag(p1)@G.T
    mu_old=G@old+fee
    old_opt=minimize(lambda x:1e4*(1.25*x@V0@x-mu_old@x), np.ones(9)/9,
                     jac=lambda x:1e4*(2.5*V0@x-mu_old), bounds=[(0,1)]*9,
                     constraints={'type':'ineq','fun':lambda x:1-x.sum(),'jac':lambda x:-np.ones(9)},
                     method='SLSQP',options={'ftol':1e-11,'maxiter':1000})
    assert old_opt.success
    xm=np.maximum(old_opt.x,0)
    if xm.sum()>1: xm/=xm.sum()
    gs=[]; mus=[]
    for a in axes(np.sqrt(p0)):
        theta=current+a
        for z in axes(np.r_[D.SF,D.SA,D.SE]):
            f=theta[:3]+z[:3]; residual=theta[3:]+z[3:9]
            observed=np.r_[f,residual]
            next_mean=future+.8*K*(observed-current)
            returns=np.r_[D.BA@f+residual,D.BE@f-D.FEE+z[9:]]
            gs.append(1+returns); mus.append(G@next_mean+fee)
    return dict(mu0=G@current+fee,V0=V0,V1=V1,g=np.array(gs).T,mu1=np.array(mus).T,
                rates=np.r_[np.full(6,5.),np.full(3,2.)]/1e4,xm=xm,hm=1-xm.sum())

def one(I, frozen=False):
    x=cp.Variable(9); u=cp.Variable(9,nonneg=True); v=cp.Variable(9,nonneg=True)
    c=I['rates']@(u+v)
    cons=[x>=0,x-I['xm']==u-v,I['hm']-cp.sum(x-I['xm'])-c>=0]
    if frozen: cons.append(x[:6]==I['xm'][:6])
    problem=cp.Problem(cp.Maximize(1e4*(I['mu0']@x-1.25*cp.quad_form(x,cp.psd_wrap(I['V0']))-c)),cons)
    problem.solve(**OPT); assert problem.status=='optimal',problem.status
    return x.value

def joint(I, fixed=None):
    n,z=I['g'].shape
    x=cp.Variable(n); u=cp.Variable(n,nonneg=True); v=cp.Variable(n,nonneg=True)
    c=I['rates']@(u+v); h=I['hm']-cp.sum(x-I['xm'])-c
    X=cp.Variable((n,z)); U=cp.Variable((n,z),nonneg=True); V=cp.Variable((n,z),nonneg=True)
    carried=cp.multiply(I['g'],cp.reshape(x,(n,1),order='F'))
    C=I['rates']@(U+V)
    cons=[x>=0,x-I['xm']==u-v,h>=0,X>=0,X-carried==U-V,h-cp.sum(X-carried,axis=0)-C>=0]
    if fixed is not None: cons.append(x==fixed)
    chol=np.linalg.cholesky(I['V1'])
    obj=I['mu0']@x-1.25*cp.quad_form(x,cp.psd_wrap(I['V0']))-c
    obj+=(cp.sum(cp.multiply(I['mu1'],X))-1.25*cp.sum_squares(chol.T@X)-cp.sum(C))/z
    problem=cp.Problem(cp.Maximize(1e4*obj),cons);problem.solve(**OPT)
    assert problem.status=='optimal',problem.status
    return x.value,problem.value

def main():
    records=[]
    for scenario in S.SCENARIOS:
        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter('always')
            I=data(scenario); my=one(I); etf=one(I,True)
            xd,V=joint(I); _,J=joint(I,my); _,JE=joint(I,etf)
        records.append(dict(scenario=scenario,initial_x=I['xm'].tolist(),myopic_x=my.tolist(),
                            dynamic_x=xd.tolist(),etf_only_x=etf.tolist(),gain_bp=V-J,
                            dynamic_value_bp=V,myopic_value_bp=J,etf_only_value_bp=JE,
                            warnings=[str(w.message) for w in caught]))
        print(scenario,f'gain={V-J:.8f} bp',flush=True)
    (S.HERE/'verification.json').write_text(json.dumps(records,indent=2)+'\n')
    if (S.HERE/'results.json').exists():
        compare()
        verify_sensitivities()

def compare():
    records=json.loads((S.HERE/'verification.json').read_text())
    results=json.loads((S.HERE/'results.json').read_text())['results']
    comparisons=[]
    for v in records:
        r=next(r for r in results if S.baseline(r) and r['scenario']==v['scenario'])
        holding=max(np.max(abs(np.array(v[p+'_x'])-r[p]['x'])) for p in ('myopic','dynamic','etf_only'))
        gain=abs(v['gain_bp']-r['gain_bp'])
        value=max(abs(v[p+'_value_bp']-r[p]['value_bp']) for p in ('myopic','dynamic','etf_only'))
        assert holding<1e-5 and gain<1e-5 and value<1e-5,(holding,gain,value)
        comparisons.append(dict(scenario=r['scenario'],max_holding_error=float(holding),
                                gain_error_bp=gain,max_value_error_bp=value))
    (S.HERE/'verification_comparison.json').write_text(json.dumps(comparisons,indent=2)+'\n')
    print('All independent baseline comparisons passed.',flush=True)

def verify_sensitivities():
    results=json.loads((S.HERE/'results.json').read_text())['results']
    selected={r['case_id']:r for r in results if r['warnings']}
    worst=max(results,key=lambda r:r['gain_bp']);selected[worst['case_id']]=worst
    records=[]
    for r in selected.values():
        assert (r['gamma'],r['uncertainty'],r['alpha_offset_bp'])==(2.5,1.,0)
        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter('always')
            I=data(r['scenario'])
            I['rates']=np.r_[np.full(6,r['fund_bp']),np.full(3,r['etf_bp'])]/1e4
            my=one(I); etf=one(I,True); xd,V=joint(I); _,J=joint(I,my); _,JE=joint(I,etf)
        holding=max(np.max(abs(x-r[p]['x'])) for x,p in ((my,'myopic'),(xd,'dynamic'),(etf,'etf_only')))
        gain=abs((V-J)-r['gain_bp'])
        value=max(abs(v-r[p]['value_bp']) for v,p in ((V,'dynamic'),(J,'myopic'),(JE,'etf_only')))
        assert holding<1e-5 and gain<1e-5 and value<1e-5,(holding,gain,value)
        records.append(dict(case_id=r['case_id'],scenario=r['scenario'],fund_bp=r['fund_bp'],etf_bp=r['etf_bp'],
                            gain_bp=V-J,max_holding_error=float(holding),gain_error_bp=gain,max_value_error_bp=value,
                            original_warning_count=len(r['warnings']),warnings=[str(w.message) for w in caught]))
        print('Additional check',r['case_id'],f'gain error {gain:.3g} bp; warnings {len(caught)}',flush=True)
    (S.HERE/'sensitivity_verification.json').write_text(json.dumps(records,indent=2)+'\n')

if __name__=='__main__': main()
