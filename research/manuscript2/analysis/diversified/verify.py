"""Independent vectorized QPs and direct diagonal-filter construction.

Uses the declared inputs, not the lab's tree, moment, policy or solve functions.
Checks all starts at the steady and manager-rotation baseline.
"""
import json,warnings
import cvxpy as cp
import numpy as np
import menu as S

OPT=dict(solver="CLARABEL",tol_gap_abs=1e-11,tol_gap_rel=1e-11,tol_feas=1e-11,max_iter=1000)

def axes(sd):
    d=len(sd)
    return [sign*np.sqrt(d)*np.eye(d)[i]*sd[i] for i in range(d) for sign in (-1,1)]

def data(forecast):
    m0=np.r_[S.LAM,S.ALPHA];p0=np.r_[S.PL_SD,S.PA_SD]**2
    noise=np.r_[S.SF,S.SA]**2
    K=p0/(p0+noise);p1=.8**2*(1-K)*p0+S.STATE_SD**2
    tb=m0.copy()
    if forecast=="manager_rotation":tb[3:]+=(S.ALPHA[[1,0,3,2,5,4]]-S.ALPHA)/.2
    B=np.vstack([S.BA,S.BE]);G=np.block([[S.BA,np.eye(6)],[S.BE,np.zeros((3,6))]])
    d=np.r_[np.zeros(6),-S.FEE]
    Vret=B@np.diag(S.SF**2)@B.T+np.diag(np.r_[S.SA**2,S.SE**2])
    V0=Vret+G@np.diag(p0)@G.T;V1=Vret+G@np.diag(p1)@G.T
    gs=[];means=[]
    for a in axes(np.sqrt(p0)):
        th=m0+a
        for z in axes(np.r_[S.SF,S.SA,S.SE]):
            f=th[:3]+z[:3];res=th[3:]+z[3:9]
            obs=np.r_[f,res]
            m1=.8*(m0+K*(obs-m0))+.2*tb
            r=np.r_[S.BA@f+res,S.BE@f-S.FEE+z[9:]]
            gs.append(1+r);means.append(G@m1+d)
    return dict(mu0=G@m0+d,V0=V0,V1=V1,g=np.array(gs).T,mu1=np.array(means).T,
                rates=np.r_[np.full(6,5.),np.full(3,2.)]/1e4)

def one(I,xm,hm):
    x=cp.Variable(9);u=cp.Variable(9,nonneg=True);v=cp.Variable(9,nonneg=True)
    c=I["rates"]@(u+v)
    cons=[x>=0,x-xm==u-v,hm-cp.sum(x-xm)-c>=0]
    pr=cp.Problem(cp.Maximize(1e4*(I["mu0"]@x-1.25*cp.quad_form(x,cp.psd_wrap(I["V0"]))-c)),cons)
    pr.solve(**OPT);assert pr.status=="optimal"
    return x.value

def joint(I,xm,hm,fixed=None):
    n,z=I["g"].shape
    x=cp.Variable(n);u=cp.Variable(n,nonneg=True);v=cp.Variable(n,nonneg=True)
    c=I["rates"]@(u+v);h=hm-cp.sum(x-xm)-c
    X=cp.Variable((n,z));U=cp.Variable((n,z),nonneg=True);V=cp.Variable((n,z),nonneg=True)
    carried=cp.multiply(I["g"],cp.reshape(x,(n,1),order="F"))
    C=I["rates"]@(U+V)
    cons=[x>=0,x-xm==u-v,h>=0,X>=0,X-carried==U-V,h-cp.sum(X-carried,axis=0)-C>=0]
    if fixed is not None:cons.append(x==fixed)
    chol=np.linalg.cholesky(I["V1"])
    obj=I["mu0"]@x-1.25*cp.quad_form(x,cp.psd_wrap(I["V0"]))-c
    obj+=(cp.sum(cp.multiply(I["mu1"],X))-1.25*cp.sum_squares(chol.T@X)-cp.sum(C))/z
    pr=cp.Problem(cp.Maximize(1e4*obj),cons);pr.solve(**OPT)
    assert pr.status=="optimal",pr.status
    return x.value,pr.value

def main():
    out=[]
    for forecast in ("steady","manager_rotation"):
        I=data(forecast)
        for start,(xm,hm) in S.STARTS.items():
            with warnings.catch_warnings(record=True) as caught:
                warnings.simplefilter("always")
                xmy=one(I,xm,hm);xd,V=joint(I,xm,hm);_,J=joint(I,xm,hm,xmy)
            out.append(dict(start=start,forecast=forecast,myopic_x=xmy.tolist(),dynamic_x=xd.tolist(),
                            gain_bp=V-J,warnings=[str(w.message) for w in caught]))
            print(start,forecast,f"gain={V-J:.7f} bp",flush=True)
    (S.HERE/"verification.json").write_text(json.dumps(out,indent=2)+"\n")

if __name__=="__main__":main()
