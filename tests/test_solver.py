from dataclasses import replace
import numpy as np
import pytest
from etfport import AllocationProblem,Moments,Portfolio,Scenario,TradingCosts,SolverError,solve_one_review,solve_two_review,compare_policies


def scalar(mean=.02, var=.04, gamma=2, holding=0, cash=1, buy=.001, sell=.002, **kw):
    return AllocationProblem(Moments([mean],[[var]]),Portfolio([holding],cash),TradingCosts([buy],[sell]),gamma,**kw)


def test_analytic_interior_purchase():
    P=scalar();r=solve_one_review(P)
    x=(.02-.001)/(.04*2)
    assert r.current.holdings[0]==pytest.approx(x,abs=1e-7)
    assert r.current.cash==pytest.approx(1-x*(1+.001),abs=1e-7)
    assert r.value==pytest.approx(.02*x-x*x*.04-.001*x,abs=1e-9)
    assert r.current.cash_multiplier<1e-7


def test_binding_budget_pays_costs_from_wealth():
    P=scalar(mean=1,var=.001,buy=.1)
    r=solve_one_review(P)
    assert r.current.holdings[0]==pytest.approx(1/1.1,abs=1e-7)
    assert r.current.cash==pytest.approx(0,abs=1e-8)
    assert r.current.cash_multiplier>0


def test_asymmetric_hold_band():
    P=scalar(mean=.0205,holding=.25,cash=.75)
    r=solve_one_review(P)
    assert r.current.trades[0]==pytest.approx(0,abs=1e-6)


def test_sale_cost_and_forced_cap_reduction():
    P=scalar(holding=.5,cash=.5,caps=np.array([.2]))
    r=solve_one_review(P)
    assert r.current.holdings[0]==pytest.approx(.2,abs=1e-7)
    assert r.current.transaction_cost==pytest.approx(.3*.002,abs=1e-8)
    assert r.current.cash==pytest.approx(.8-.3*.002,abs=1e-7)
    with pytest.raises(SolverError,match='infeasible'):solve_one_review(P,frozen=(0,))


def test_etf_only_freezes_dollars_and_sales_fund_purchases():
    P=AllocationProblem(Moments([.03,.01],[[.003,0],[0,.002]]),Portfolio([.3,.7],0),TradingCosts([.0005,.0002],[.0005,.0002]),2.5,fund_indices=(0,))
    etf=solve_one_review(P,frozen=P.fund_indices);joint=solve_one_review(P)
    assert etf.current.holdings[0]==pytest.approx(.3,abs=1e-8)
    assert joint.current.holdings[0]>.3
    assert joint.current.holdings[1]<.7
    for r in (etf,joint):
        assert r.current.holdings.sum()+r.current.cash+r.current.transaction_cost==pytest.approx(1,abs=1e-10)


def test_marking_probabilities_discount_and_conditional_duals():
    P=scalar(mean=.025,var=.005,holding=.6,cash=.4,buy=.003,sell=.001,discount=.7,
      scenarios=(Scenario(.25,[.8],Moments([.03],[[.004]])),Scenario(.75,[1.2],Moments([.04],[[.008]]))))
    fixed=np.array([.7]);result=solve_two_review(P,first_holdings=fixed)
    total=result.current.score
    for state,action in zip(P.scenarios,result.future):
        future_problem=replace(P,moments=state.moments,portfolio=Portfolio(state.gross_returns*fixed,max(result.current.cash,0)),scenarios=())
        standalone=solve_one_review(future_problem)
        assert action.holdings==pytest.approx(standalone.current.holdings,abs=1e-6)
        assert action.cash_multiplier==pytest.approx(standalone.current.cash_multiplier,abs=1e-6)
        total+=P.discount*state.probability*standalone.value
    assert result.value==pytest.approx(total,abs=1e-8)
    assert result.current.cash_multiplier is None
    assert result.effective_cash_multiplier is None
    assert result.max_accounting_error<1e-8


def test_monetary_unit_invariance_requires_gamma_rescaling():
    P=scalar()
    r=solve_one_review(P)
    R=replace(P,portfolio=Portfolio(P.portfolio.holdings*100,100),gamma=P.gamma/100)
    big=solve_one_review(R)
    assert big.current.holdings/100==pytest.approx(r.current.holdings,abs=1e-6)
    assert big.value/100==pytest.approx(r.value,abs=1e-8)


def test_two_review_and_comparison_dominate_feasible_benchmarks():
    P=scalar(scenarios=(Scenario(1,[1.02],Moments([.018],[[.035]])),),fund_indices=(0,))
    r=compare_policies(P)
    assert r.planning_gain_bp>=-1e-5
    assert r.current_fund_benefit_bp>=-1e-5
    assert r.etf_only.current.holdings[0]==pytest.approx(0,abs=1e-7)
    assert r.planning.value>=r.one_review.value-1e-8
    assert r.to_dict()['planning']['future'][0]['holdings']


def test_missing_future_and_invalid_frozen_indices():
    with pytest.raises(ValueError,match='future scenarios'):solve_two_review(scalar())
    with pytest.raises(ValueError,match='Frozen'):solve_one_review(scalar(),frozen=(1,))
