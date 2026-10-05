# Using ETFPort

## State the problem in consistent units

All positions and caps are **dollar amounts in one fixed wealth unit**, not
portfolio weights. The example starts with wealth one; output trade percentages
are divided by that initial wealth. Means and cost rates are decimals per
quarter or per trade: 5 bp is 0.0005. Covariance inputs are variances, not standard
deviations. Alpha is net of internal fund expenses; investor switching costs
are separate. `predictive_moments` deducts ETF fees once.

The score is `mean @ holdings - gamma/2 * holdings @ covariance @ holdings - costs`.
Gamma is a dollar-quadratic coefficient, not an estimated CRRA parameter. If all
dollar units are multiplied by 100, divide gamma by 100 to preserve weights.
Cash has zero excess return and remains unchanged between the two reviews.

```python
from etfport import AllocationProblem, Moments, Portfolio, TradingCosts, solve_one_review

problem = AllocationProblem(
    moments=Moments([0.013, 0.0118], [[0.007, 0.0064], [0.0064, 0.0065]]),
    portfolio=Portfolio([0.3, 0.7], cash=0.0),
    costs=TradingCosts(buy=[0.0005, 0.0002], sell=[0.0005, 0.0002]),
    gamma=2.5,
    names=("Active fund", "Equity ETF"),
    fund_indices=(0,),
)
result = solve_one_review(problem)
print(result.current.holdings, result.current.cash)
```

There is no borrowing or shorting. Holdings plus cash plus current transaction
costs equal pre-trade wealth. A purchase needs cash or sale proceeds. Caps are
optional; an incumbent above its cap requires a funded corrective sale. Freezing
an instrument above its cap can make the problem infeasible.

## Supply future information explicitly

`solve_two_review` requires a tuple of `Scenario` objects. Each has:

- A strictly positive probability; probabilities sum to one.
- Positive instrument gross returns between reviews, for marking carried holdings.
- The **next review's** `Moments`, after applying your specified information update.
- An optional readable label.

A scenario must represent information the manager actually observes before
choosing its next trade. Do not create separate decision nodes for latent
outcomes that cannot be distinguished by those observations. The optimizer
cannot infer your filtration or check whether a forecast contains future data.
For indistinguishable outcomes, first construct a single observable state with
appropriate score inputs and carried holdings.

The final review earns one more quarterly score. There is no terminal liquidation
cost or value after that score. The future actions respect the same long-only
bounds, dollar caps and purchase/sale rates. Future covariance can differ by
state. A discount factor in (0, 1] scales the expected final score.

## Compare policies on the same objective

`compare_policies(problem)` evaluates three policies:

1. ETF-only today: freeze `fund_indices`, optimize the remaining instruments,
   and trade all instruments optimally next review.
2. Repeated one-review: optimize today without continuation, then optimize again
   from that policy's marked holdings and cash.
3. Planning: optimize both reviews jointly, respecting funding in every state.

`current_fund_benefit_bp` compares the **current** joint and ETF-only scores.
`planning_gain_bp` compares the **two-review** planned and repeated-one-review
values. Both are divided by initial wealth and multiplied by 10,000. Costs are
already deducted. Neither quantity is an annualized or realized investment return.
The three future policies generally start from different portfolios.

## Diagnostics and numerical precision

`PolicyResult` provides current and state-contingent allocations, cash, costs,
scores, probabilities, solver status, recorded warnings and reconstructed
accounting error. Small negative cash or positions within solver tolerance may
be reported rather than silently changing the policy. Violations greater than
2e-7 times max(1, initial wealth) cause `SolverError`.

Only an `optimal` solver status is accepted; infeasible and `optimal_inaccurate`
results raise `SolverError`. Use `SolverOptions` to change tolerances explicitly.
Covariances must be positive definite for `Moments`; primitive factor covariance
blocks may be positive semidefinite. Inputs are copied and validated, and are
not altered by optimization.

Cash multipliers are in marginal score units per additional dollar of funding.
Next-state multipliers are normalized for scenario probability, discounting and
objective scaling. The effective dynamic cash price adds expected discounted
future cash value to the current root multiplier. Multipliers may be nonunique.
When today's holdings are fixed to evaluate a policy, its root multiplier is
not meaningful and is `None`. In `compare_policies`, the separately solved
one-review root multiplier is reported for each one-review benchmark; its
`effective_cash_multiplier` remains `None`.

## JSON and command line

The [input example](../examples/custom_problem.json) defines the schema. Omit
`caps` for no upper caps, or use JSON `null` for individual uncapped positions.
`fund_indices` are zero-based indices. `mean` and `covariance` at the top level
are today's inputs; each scenario supplies its own means and covariance.

```sh
etfport solve examples/custom_problem.json --horizon one
etfport solve examples/custom_problem.json --horizon compare --output result.json
etfport example --scenario style_up --output style.json
```

JSON output contains all future state actions. `python -m etfport` is equivalent
to the installed `etfport` command. Example inputs are hypothetical and should
not be interpreted as recommendations for fund selection.
