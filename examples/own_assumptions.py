"""Editable input tutorial; all numbers and the forecast revision rule are assumed.

Run after installing etfport: python examples/own_assumptions.py
Writes my_result.json in the current directory. No market data are downloaded.
"""
from dataclasses import replace
from pathlib import Path
import json

import numpy as np
from etfport import (
    AllocationProblem, Portfolio, Scenario, TradingCosts,
    compare_policies, predictive_moments, solve_one_review,
)

# BEGIN current-inputs
# Instrument order everywhere: Equity fund, Bond fund, Equity ETF, Bond ETF.
# Factor order: equity, duration. All return inputs refer to ONE QUARTER.
premium_mean = np.array([0.015, 0.005])
alpha_mean = np.array([0.001, 0.0005])  # already net of internal fund expenses


def make_moments(premia, alphas):
    return predictive_moments(
        fund_loadings=[[1.0, 0.1], [0.2, 0.9]],
        etf_loadings=[[1.0, 0.0], [0.0, 1.0]],
        premium_mean=premia,
        alpha_mean=alphas,
        factor_covariance=np.diag(np.array([0.08, 0.03]) ** 2),
        fund_residual_covariance=np.diag(np.array([0.02, 0.015]) ** 2),
        etf_residual_covariance=np.diag(np.array([0.001, 0.001]) ** 2),
        premium_uncertainty=np.diag(np.array([0.003, 0.002]) ** 2),
        alpha_uncertainty=np.diag(np.array([0.0005, 0.0005]) ** 2),
        etf_fees=[0.0001, 0.0002],  # quarterly fees; deducted by this helper
    )


today = make_moments(premium_mean, alpha_mean)
problem = AllocationProblem(
    moments=today,
    portfolio=Portfolio([0.25, 0.25, 0.25, 0.20], cash=0.05),
    costs=TradingCosts(
        buy=[0.0005, 0.0005, 0.0002, 0.0002],
        sell=[0.0005, 0.0005, 0.0002, 0.0002],
    ),
    gamma=2.5,
    names=("Equity fund", "Bond fund", "Equity ETF", "Bond ETF"),
    fund_indices=(0, 1),  # zero-based indices; remaining instruments are ETFs
)  # no position caps unless you explicitly supply caps=
allocation = solve_one_review(problem).current
print("Names:", problem.names)
print("New holdings:", allocation.holdings)
print("Trades (+ buy / - sell):", allocation.trades)
print("Cash:", allocation.cash, "Trading cost:", allocation.transaction_cost)
# END current-inputs

# BEGIN future-inputs
# Eight equally likely return outcomes matching today's mean and covariance.
# This finite law is an illustrative assumption, not a fitted return model.
n = len(today.mean)
L = np.linalg.cholesky(today.covariance)
states = []
for i in range(n):
    for sign in (-1, 1):
        returns = today.mean + sign * np.sqrt(n) * L[:, i]
        # An assumed revision rule: react to observed ETF return surprises.
        # 0.25 is a chosen response coefficient, NOT an estimated Kalman gain.
        next_premia = premium_mean + 0.25 * (returns[2:] - today.mean[2:])
        states.append(Scenario(
            probability=1 / (2 * n),
            gross_returns=1 + returns,
            moments=make_moments(next_premia, alpha_mean),
            label=f"return direction {i}, sign {sign:+d}",
        ))

planning_problem = replace(problem, scenarios=tuple(states), discount=1.0)
comparison = compare_policies(planning_problem)
print("ETF-only trades:", comparison.etf_only.current.trades)
print("One-review trades:", comparison.one_review.current.trades)
print("Planning trades:", comparison.planning.current.trades)
print("Current fund-trading benefit (score bp):", comparison.current_fund_benefit_bp)
print("Two-review planning gain (score bp):", comparison.planning_gain_bp)
# END future-inputs

# BEGIN inspect-future
for state, action in zip(planning_problem.scenarios, comparison.planning.future):
    print(state.label, "probability:", state.probability,
          "future trades:", action.trades, "future cash:", action.cash)

output = comparison.to_dict()
output["names"] = list(problem.names)
output["scenario_labels"] = [state.label for state in planning_problem.scenarios]
Path("my_result.json").write_text(json.dumps(output, indent=2, allow_nan=False) + "\n")
# END inspect-future
