import numpy as np
import pytest
from etfport import AllocationProblem,Moments,Portfolio,Scenario,TradingCosts,predictive_moments


@pytest.mark.parametrize('mean,cov', [([np.nan],[[1]]),([1],[[0]]),([1,2],[[1,1],[0,1]]),([1],[[np.inf]])])
def test_invalid_moments(mean,cov):
    with pytest.raises(ValueError):Moments(mean,cov)

@pytest.mark.parametrize('x,h',[([-1],1),([0],-1),([0],0),([np.inf],0),([1],np.nan)])
def test_invalid_portfolio(x,h):
    with pytest.raises(ValueError):Portfolio(x,h)

@pytest.mark.parametrize('buy,sell',[([-1],[0]),([0],[1]),([np.nan],[0]),([0,0],[0])])
def test_invalid_costs(buy,sell):
    with pytest.raises(ValueError):TradingCosts(buy,sell)


def test_input_arrays_are_copied_and_immutable():
    a=np.array([.01]);m=Moments(a,[[.1]]);a[0]=100
    assert m.mean[0]==.01
    with pytest.raises(ValueError):m.mean[0]=2


def test_probability_and_solvency_validation():
    m=Moments([.01],[[.1]])
    for q,g in [(0,[1]),(-.1,[1]),(1,[0]),(1,[np.nan])]:
        with pytest.raises(ValueError):Scenario(q,g,m)
    with pytest.raises(ValueError,match='sum to one'):
        AllocationProblem(m,Portfolio([0],1),TradingCosts([0],[0]),2,scenarios=(Scenario(.5,[1],m),))


def test_factor_risk_uncertainty_and_fees_are_counted_once():
    m=predictive_moments(fund_loadings=[[2]],etf_loadings=[[1]],premium_mean=[.01],alpha_mean=[.003],
      factor_covariance=[[.01]],fund_residual_covariance=[[.002]],etf_residual_covariance=[[.001]],
      premium_uncertainty=[[.004]],alpha_uncertainty=[[.005]],etf_fees=[.0002])
    assert m.mean==pytest.approx([.023,.0098])
    assert m.covariance==pytest.approx(np.array([[4*.014+.007,2*.014],[2*.014,.015]]))
