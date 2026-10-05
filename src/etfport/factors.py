"""Predictive moments with distinct factor risk and mean-estimation uncertainty."""
import numpy as np
from .models import Moments, covariance, vector


def predictive_moments(*, fund_loadings, etf_loadings, premium_mean, alpha_mean,
                       factor_covariance, fund_residual_covariance, etf_residual_covariance,
                       premium_uncertainty, alpha_uncertainty, etf_fees):
    """Construct manuscript Equation (2), with funds ordered before ETFs.

    Alpha is already net of internal fund expenses. ETF fees are deducted once.
    Residual shocks and the two mean-error blocks are assumed uncorrelated.
    Arbitrary within-block covariances are allowed; this does not extend the
    paper's diagonal-only closed-form results. Supply Moments directly for a
    different predictive covariance model.
    """
    lam=vector(premium_mean,'premium_mean');alpha=vector(alpha_mean,'alpha_mean')
    BA=np.asarray(fund_loadings,dtype=float);BE=np.asarray(etf_loadings,dtype=float)
    n=len(alpha);k=len(lam)
    if BA.shape!=(n,k) or BE.ndim!=2 or BE.shape[1]!=k or BE.shape[0]<1 or not np.isfinite(BA).all() or not np.isfinite(BE).all():
        raise ValueError('Loadings must have funds/ETFs in rows and one column per factor')
    m=BE.shape[0]
    fee=vector(etf_fees,'etf_fees',m,nonnegative=True)
    sf=covariance(factor_covariance,'factor_covariance',k)
    sa=covariance(fund_residual_covariance,'fund_residual_covariance',n)
    se=covariance(etf_residual_covariance,'etf_residual_covariance',m)
    pl=covariance(premium_uncertainty,'premium_uncertainty',k)
    pa=covariance(alpha_uncertainty,'alpha_uncertainty',n)
    B=np.vstack([BA,BE]);cov=B@(sf+pl)@B.T
    cov[:n,:n]+=sa+pa;cov[n:,n:]+=se
    return Moments(np.r_[BA@lam+alpha,BE@lam-fee],cov)
