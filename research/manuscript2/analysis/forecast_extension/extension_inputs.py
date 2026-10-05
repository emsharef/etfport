"""Prespecified forecast and missing-span inputs; see DESIGN.md."""
from pathlib import Path
import sys
import numpy as np
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
sys.path.insert(0,str(HERE.parent/'diversified'))
import menu as D
NAMES=D.NAMES
STYLE=np.array([.5,-.5,0,0,.4,-.4])

def arrays(c,old=False):
    style=c['menu']=='unspanned'
    BA=np.column_stack([D.BA,STYLE]) if style else D.BA.copy()
    BE=np.column_stack([D.BE,np.zeros(3)]) if style else D.BE.copy()
    lam=np.r_[D.LAM,0.] if style else D.LAM.copy()
    alpha=D.ALPHA.copy()
    sf=np.r_[D.SF,.03] if style else D.SF.copy()
    ps=np.r_[D.PL_SD,c['style_prior_bp']/1e4] if style else D.PL_SD.copy()
    qs=np.r_[D.STATE_SD[:3],.0005,D.STATE_SD[3:]] if style else D.STATE_SD.copy()
    prior=np.r_[lam,alpha]; current=prior.copy(); K=len(lam)
    if not old:
        if style:
            current[3]+=c['revision_bp']/1e4
        elif c['scenario'].startswith(('duration','credit_premium')):
            delta=np.zeros(3);delta[1 if c['scenario'].startswith('duration') else 2]=c['revision_bp']/1e4
            current[:3]+=np.linalg.solve(D.BE,delta)
        elif c['scenario'].startswith('credit_alpha'):
            current[K+4]+=c['revision_bp']/1e4
        else: assert c['scenario']=='unchanged'
    tb=prior if c['persistence']=='reverting' else current.copy()
    return dict(BA=BA,BE=BE,m=current,tb=tb,sf=sf,ps=ps,qs=qs)

def build(c,old=False,free=False):
    a=arrays(c,old);K=a['BA'].shape[1]
    rates=np.r_[np.full(6,c['fund_bp']),np.full(3,c['etf_bp'])]/1e4
    if free:rates*=0
    return D.mn_model(BA=a['BA'],BE=a['BE'],lam=a['m'][:K],alpha=a['m'][K:],
                      premium_sd=a['ps'],alpha_sd=D.PA_SD,sigma_f=a['sf'],sigma_A=D.SA,
                      sigma_E=D.SE,cE=D.FEE,gamma=2.5,beta=1.,kp=rates,km=rates,
                      cap=np.full(9,np.inf),phi=np.full(K+6,.8),q=a['qs']**2,
                      theta_bar=a['tb'],law='axis',observe_factor=True)

def cases():
    out=[]
    for name,bp in [('unchanged',0),('duration_up',10),('duration_down',-10),
                    ('credit_premium_up',15),('credit_premium_down',-15),
                    ('credit_alpha_up',5),('credit_alpha_down',-5)]:
        out.append(dict(menu='spanned',scenario=name,revision_bp=bp,style_prior_bp=0,persistence='persistent'))
    for sd in (10,20,40):
        for persistence in ('persistent','reverting'):
            for bp in (-40,-20,-10,0,10,20,40):
                out.append(dict(menu='unspanned',scenario='style',revision_bp=bp,style_prior_bp=sd,persistence=persistence))
    assert len(out)==49
    return [dict(case_id=i,block=c['menu'],gamma=2.5,uncertainty=1.,alpha_offset_bp=0,
                 fund_bp=5.,etf_bp=2.,**c) for i,c in enumerate(out)]
