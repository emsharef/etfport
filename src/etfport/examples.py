"""Assumed six-fund/three-ETF cases from the manuscript, not market estimates."""
import numpy as np
from .models import AllocationProblem, Moments, Portfolio, Scenario, TradingCosts
from .solver import solve_one_review
from .factors import predictive_moments

SCENARIOS=('unchanged','premium_down_persistent','premium_up_persistent',
           'premium_down_reverting','premium_up_reverting','alpha_up','alpha_down',
           'anticipated_down','anticipated_up','style_up','style_down')


def _axes(sd):
    return [sign*np.sqrt(len(sd))*np.eye(len(sd))[i]*sd[i] for i in range(len(sd)) for sign in (-1,1)]


def make_example(scenario='premium_down_persistent'):
    """Return a complete two-review problem using the published assumed inputs.

    Means evolve with persistence 0.8 and a diagonal linear filter. The finite
    axis law preserves the specified first/second moments; the filter is not
    its exact Bayesian posterior. Forecast revisions are conditional inputs.
    In style_up/down the extra factor's premium is revised by +/-10 bp.
    """
    if scenario not in SCENARIOS:raise ValueError(f'Unknown scenario: {scenario}')
    BE=np.array([[1,0,0],[0,1,0],[.2,4/15,1.]])
    Q=np.array([[1.05,0,0],[.9,.05,.1],[0,1.1,0],[.05,.9,.05],[.05,0,1],[0,.15,.9]])
    BA=Q@BE;lam=np.array([.012,.003,.0028]);sf=np.array([.08,.03,np.sqrt(.00128)])
    ps=np.array([.004,.0015,.002]);qs=np.array([.001,.0005,.0008])
    if scenario.startswith('style_'):
        BA=np.column_stack([BA,[.5,-.5,0,0,.4,-.4]]);BE=np.column_stack([BE,np.zeros(3)])
        lam=np.r_[lam,0.];sf=np.r_[sf,.03];ps=np.r_[ps,.002];qs=np.r_[qs,.0005]
    k=len(lam);alpha=np.array([4,2,1,.5,3,1])/1e4
    sa=np.array([.04,.05,.015,.02,.025,.03]);pas=np.array([20,30,10,15,15,25])/1e4
    se=np.array([.001,.0005,.001]);fees=np.array([2,1,3])/1e4
    names=('Equity A','Equity B','Duration A','Duration B','Credit A','Credit B','Equity ETF','Duration ETF','Credit ETF')
    old=np.r_[lam,alpha];current=old.copy();future=old.copy()
    if scenario.startswith(('premium_','anticipated_')):
        direction=-1 if '_up' in scenario else 1
        delta=np.linalg.solve(BE,direction*np.array([-.0015,.0005,0]))
        if scenario.startswith('anticipated_'):future[:k]+=delta
        else:
            current[:k]+=delta;future[:k]+=delta*(.8 if scenario.endswith('reverting') else 1)
    elif scenario.startswith('alpha_'):
        current[k]+=.0005 if scenario=='alpha_up' else -.0005;future=current.copy()
    elif scenario.startswith('style_'):
        current[3]+=.001 if scenario=='style_up' else -.001;future=current.copy()
    p0=np.r_[ps,pas]**2;gain=p0/(p0+np.r_[sf,sa]**2)
    p1=.64*(1-gain)*p0+np.r_[qs,np.full(6,.0005)]**2
    def moments(mean,p):
        return predictive_moments(fund_loadings=BA,etf_loadings=BE,premium_mean=mean[:k],alpha_mean=mean[k:],
          factor_covariance=np.diag(sf**2),fund_residual_covariance=np.diag(sa**2),etf_residual_covariance=np.diag(se**2),
          premium_uncertainty=np.diag(p[:k]),alpha_uncertainty=np.diag(p[k:]),etf_fees=fees)
    initial=AllocationProblem(moments(old,p0),Portfolio(np.zeros(9),1.),TradingCosts(np.zeros(9),np.zeros(9)),2.5,names,tuple(range(6)))
    x=np.maximum(solve_one_review(initial).current.holdings,0)
    if x.sum()>1:x/=x.sum()
    P=Portfolio(x,1-float(x.sum()))
    next_cov=moments(future,p1).covariance
    param=_axes(np.sqrt(p0));shocks=_axes(np.r_[sf,sa,se]);count=len(param)*len(shocks)
    states=[]
    for a in param:
        theta=current+a
        for z in shocks:
            f=theta[:k]+z[:k];residual=theta[k:]+z[k:k+6]
            observed=np.r_[f,residual];next_mean=future+.8*gain*(observed-current)
            mu=np.r_[BA@next_mean[:k]+next_mean[k:],BE@next_mean[:k]-fees]
            returns=np.r_[BA@f+residual,BE@f-fees+z[k+6:]]
            states.append(Scenario(1/count,1+returns,Moments(mu,next_cov)))
    costs=TradingCosts(np.r_[np.full(6,.0005),np.full(3,.0002)],np.r_[np.full(6,.0005),np.full(3,.0002)])
    return AllocationProblem(moments(current,p0),P,costs,2.5,names,tuple(range(6)),scenarios=tuple(states))
