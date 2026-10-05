"""Independent 3/4-factor tree and filter, reusing the checked vectorized QP only."""
import json
import importlib.util
import sys
import warnings
import numpy as np
from scipy.optimize import minimize
import extension_inputs as S
sys.path.insert(0,str(S.HERE.parent/'forecast_revision'))
_module_spec=importlib.util.spec_from_file_location('prior_forecast_verification',S.HERE.parent/'forecast_revision/verify.py')
QP=importlib.util.module_from_spec(_module_spec)
_module_spec.loader.exec_module(QP)
QP.OPT.update(tol_gap_abs=1e-9,tol_gap_rel=1e-9,tol_feas=1e-10,max_iter=1000)

def data(c):
    D=S.D;unspanned=c['menu']=='unspanned'
    BA=np.column_stack([D.BA,[.5,-.5,0,0,.4,-.4]]) if unspanned else D.BA
    BE=np.column_stack([D.BE,np.zeros(3)]) if unspanned else D.BE
    K=BA.shape[1]
    factor_mean=np.r_[D.LAM,0.] if unspanned else D.LAM
    sf=np.r_[D.SF,.03] if unspanned else D.SF
    ps=np.r_[D.PL_SD,c['style_prior_bp']/1e4] if unspanned else D.PL_SD
    qs=np.r_[D.STATE_SD[:3],.0005,D.STATE_SD[3:]] if unspanned else D.STATE_SD
    old=np.r_[factor_mean,D.ALPHA];current=old.copy()
    if unspanned:
        current[3]+=c['revision_bp']/1e4
    elif c['scenario'].startswith('duration'):
        current[:3]+=np.linalg.inv(D.BE)@np.array([0,c['revision_bp']/1e4,0])
    elif c['scenario'].startswith('credit_premium'):
        current[:3]+=np.linalg.inv(D.BE)@np.array([0,0,c['revision_bp']/1e4])
    elif c['scenario'].startswith('credit_alpha'):
        current[K+4]+=c['revision_bp']/1e4
    else:assert c['scenario']=='unchanged'
    future=old+.8*(current-old) if c['persistence']=='reverting' else current.copy()
    p0=np.r_[ps,D.PA_SD]**2
    gain=p0/(p0+np.r_[sf,D.SA]**2)
    p1=.64*(1-gain)*p0+qs**2
    B=np.vstack([BA,BE]);G=np.block([[BA,np.eye(6)],[BE,np.zeros((3,6))]])
    fee=np.r_[np.zeros(6),-D.FEE]
    Vr=B@np.diag(sf**2)@B.T+np.diag(np.r_[D.SA**2,D.SE**2])
    V0=Vr+G@np.diag(p0)@G.T;V1=Vr+G@np.diag(p1)@G.T
    mu=G@old+fee
    opt=minimize(lambda x:1e4*(1.25*x@V0@x-mu@x),np.ones(9)/9,
                 jac=lambda x:1e4*(2.5*V0@x-mu),bounds=[(0,1)]*9,
                 constraints={'type':'ineq','fun':lambda x:1-x.sum(),'jac':lambda x:-np.ones(9)},
                 method='SLSQP',options={'ftol':1e-9,'maxiter':1000})
    assert opt.success,opt.message
    # Polish the independent static solution by solving its active-set KKT system.
    # Check all inactive inequalities as well, rather than trusting the SLSQP support.
    active=np.flatnonzero(opt.x>1e-6);A=2.5*V0[np.ix_(active,active)]
    xm=np.zeros(9)
    if opt.x.sum()>1-1e-6:
        system=np.block([[A,np.ones((len(active),1))],[np.ones((1,len(active))),np.zeros((1,1))]])
        solved=np.linalg.solve(system,np.r_[mu[active],1.])
        xm[active]=solved[:-1];eta=solved[-1]
    else:
        xm[active]=np.linalg.solve(A,mu[active]);eta=0.
    residual=mu-2.5*V0@xm-eta
    inactive=np.setdiff1d(np.arange(9),active)
    assert min(xm)>=-1e-12 and eta>=-1e-12 and xm.sum()<=1+1e-12
    assert max(abs(residual[active]))<1e-10
    assert len(inactive)==0 or max(residual[inactive])<1e-10
    if xm.sum()>1:xm/=xm.sum()
    gs=[];mus=[]
    for atom in QP.axes(np.sqrt(p0)):
        theta=current+atom
        for z in QP.axes(np.r_[sf,D.SA,D.SE]):
            f=theta[:K]+z[:K];a=theta[K:]+z[K:K+6]
            next_mean=future+.8*gain*(np.r_[f,a]-current)
            ret=np.r_[BA@f+a,BE@f-D.FEE+z[K+6:]]
            gs.append(1+ret);mus.append(G@next_mean+fee)
    return dict(mu0=G@current+fee,V0=V0,V1=V1,g=np.array(gs).T,mu1=np.array(mus).T,
                rates=np.r_[np.full(6,5.),np.full(3,2.)]/1e4,xm=xm,hm=1-xm.sum())

def main():
    records=[]
    for c in S.cases():
        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter('always')
            I=data(c);my=QP.one(I);etf=QP.one(I,True)
            xd,V=QP.joint(I);_,J=QP.joint(I,my);_,JE=QP.joint(I,etf)
        records.append(dict(case_id=c['case_id'],myopic_x=my.tolist(),dynamic_x=xd.tolist(),
                            etf_only_x=etf.tolist(),gain_bp=V-J,myopic_value_bp=J,dynamic_value_bp=V,
                            etf_only_value_bp=JE,warnings=[str(w.message) for w in caught]))
        print(c['case_id'],c['scenario'],c['revision_bp'],f'gain={V-J:.6f} bp',flush=True)
    (S.HERE/'verification.json').write_text(json.dumps(records,indent=2)+'\n')
    if (S.HERE/'results.json').exists():compare()

def compare():
    rows={r['case_id']:r for r in json.loads((S.HERE/'results.json').read_text())['results']}
    vv=json.loads((S.HERE/'verification.json').read_text());out=[]
    for v in vv:
        r=rows[v['case_id']]
        h=max(np.max(abs(np.array(v[p+'_x'])-r[p]['x'])) for p in ('myopic','dynamic','etf_only'))
        value=max(abs(v[p+'_value_bp']-r[p]['value_bp']) for p in ('myopic','dynamic','etf_only'))
        gain=abs(v['gain_bp']-r['gain_bp'])
        assert h<1e-5 and value<1e-5 and gain<1e-5,(v['case_id'],h,value,gain)
        out.append(dict(case_id=v['case_id'],holding_error=float(h),value_error_bp=value,gain_error_bp=gain))
    (S.HERE/'verification_comparison.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent checks passed.',flush=True)

if __name__=='__main__':main()
