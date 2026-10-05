# ETFPort

**Portfolio allocation across active funds and ETFs with uncertain forecasts.**

ETFPort solves long-only, fully funded quarterly allocation problems with
instrument-specific purchase and sale costs. It compares an ETF-only adjustment,
joint one-quarter optimization, and planning over two reviews with funded trades
in every future state. A factor-model helper keeps mean-estimation uncertainty
separate from realized-return risk when constructing predictive moments.

| Paper | Read | Source |
|---|---|---|
| **When Forecasts Change: Rebalancing Active Funds and ETFs** — the standalone article | [PDF](papers/manuscript/paper.pdf) | [Markdown](papers/manuscript/MANUSCRIPT.md) · [LaTeX](papers/manuscript/main.tex) |
| **Quarterly portfolio construction with uncertain alpha and factor premia** — the full lab research record | [PDF](papers/lab/paper.pdf) | [Markdown](papers/lab/PAPER.md) · [LaTeX](papers/lab/main.tex) |

The article gives conditional allocation tests and bounds. The calculations use
**assumed inputs**, not estimated fund data. Visible allocation changes can have
small score benefits: the published two-review planning gains are below one
basis point in the two forecast-revision grids. These are differences in an
additive quarterly mean–variance objective, already net of costs—not realized
returns, terminal-wealth utility gains or forecasts of investment performance.

## Install

Python 3.12 or newer:

```sh
python -m pip install "git+https://github.com/emsharef/etfport.git"
```

## Use your own assumptions

Start with your current holdings and your estimates for the next quarter.
The following is a complete example with **two funds, two ETFs and cash**;
replace its assumed inputs with yours. It does not depend on a paper preset.
The [complete runnable script](examples/own_assumptions.py) includes both
one-review allocation and planning, and saves the results to JSON.

### 1. Enter your forecasts and solve today's allocation

Use **quarterly decimal returns**: `0.015` means 1.5% per quarter, and a trade
cost of `0.0005` means 5 basis points of the amount traded. Covariances are
squared-return units. Normalize starting wealth to one, as below: `0.25` is
25% of starting wealth. After trading, holdings plus cash plus trading costs
sum to that starting wealth. Future positions use the same fixed wealth unit.

```python
import numpy as np
from etfport import (
    AllocationProblem, Portfolio, TradingCosts,
    predictive_moments, solve_one_review,
)

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
```

The three return-risk covariance inputs describe fluctuations **conditional on
the unknown means**. `premium_uncertainty` and `alpha_uncertainty` describe
uncertainty about those means. The helper combines them into a predictive
covariance under its stated independence assumptions. In the example, an
8% quarterly factor volatility is squared as `0.08**2`; a 0.3-percentage-point
standard deviation of the estimated quarterly premium is squared as `0.003**2`.
These are different inputs, not interchangeable volatility estimates.

The diagonal matrices above are chosen for illustration. You can supply
correlated inputs within each block. If you already have instrument-level
predictive means and covariance, use `Moments(your_means, your_covariance)`
instead of the helper. Do not add mean uncertainty again if it is already in
that predictive covariance. See the [input guide](docs/using-your-own-inputs.md)
for dimensions, fees, correlations, unspanned factors and wealth scaling.

### 2. Add your assumptions about the next review

Planning needs a **joint distribution of intervening returns and the forecasts
available at the next review**. Each `Scenario` supplies its probability,
instrument gross returns for marking today's holdings, and the next review's
conditional `Moments`. The software does not estimate this distribution for you.

The following continues the code above. It uses eight return outcomes matching
today's predictive mean and covariance, then applies an explicitly assumed
forecast-revision rule. Replace that rule and the finite law with your own
model. This is a runnable input illustration, not a Bayesian learning model or
an empirical calibration.

```python
from dataclasses import replace
from etfport import Scenario, compare_policies

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
```

`comparison.planning.current` is today's planned action.
`comparison.planning.future[j]` is the action at future scenario `j`, after
marking holdings by that scenario's returns. Each action includes holdings,
trades, cash, transaction cost and score. `comparison.to_dict()` includes all
three policies and all future actions and can be saved as JSON.

The two printed benefits answer different questions: the current score benefit
of allowing fund trades, and the extra two-review score from planning ahead.
They already deduct trading costs. They are **not realized returns**. See
[policy interpretation](docs/using-the-package.md#compare-policies-on-the-same-objective).

### 3. Or edit a JSON file and use the command line

From a repository checkout, copy the [JSON template](examples/custom_problem.json):

```sh
cp examples/custom_problem.json my_portfolio.json
# Edit my_portfolio.json with your holdings, forecasts, covariance and costs.
etfport solve my_portfolio.json --horizon one --output my_allocation.json
# After supplying scenarios in the file:
etfport solve my_portfolio.json --horizon compare --output my_comparison.json
```

Use `--horizon two` for the planned policy alone. The
[JSON field guide](docs/using-your-own-inputs.md#json-input-fields) explains every
field. JSON accepts instrument-level moments; use Python's `predictive_moments`
if your inputs are factor premia, loadings and fund alpha estimates.

## Reproduce the paper or develop the package

```sh
etfport example --scenario premium_down_persistent --output paper_result.json
```

Other paper scenarios include `unchanged`, `alpha_up`, `alpha_down`, `style_up`,
and `style_down`. These commands use the article's assumed inputs.

For a checkout containing the editable examples, papers and tests:

```sh
git clone https://github.com/emsharef/etfport.git
cd etfport
python -m venv .venv
. .venv/bin/activate
python -m pip install -e ".[dev,research]"
python examples/own_assumptions.py
pytest
python scripts/check_package.py
```

The [usage guide](docs/using-the-package.md) covers the objective, funding and
solver diagnostics. The [model and scope guide](docs/model-and-scope.md) explains
the relationship between the implemented programs and the formal theorems.

## Papers, proofs and reproduction

- [Reproduction guide](docs/reproducing.md): examples, all 157 forecast cases,
  independent numerical checks, figures and PDF builds.
- [Proof map](docs/proof-map.md): article results linked to exact Lean sources.
- [Formalization guide](docs/formalization.md): pinned toolchain, explicit
  upstream hypotheses and the boundary of machine checking.
- [Numerical supplement](papers/manuscript/NUMERICAL_SUPPLEMENT.md): complete
  trade tables, score comparisons and funding diagnostics.
- [Research archive guide](docs/research-archive.md): broader lab claims,
  checks and the later integrated allocation analysis.
- [Release validation](docs/validation.md): checks run and their limits.

The Python optimizer is numerical software, **not formally verified Python**.
The Lean project proves the encoded mathematical statements under their stated
hypotheses. No theorem is claimed for an arbitrary long-horizon funded policy.

| Directory | Contents |
|---|---|
| `src/etfport/` | Installable API and command-line application |
| `examples/` | Explicit user-input example |
| `tests/` | Accounting, feasibility, analytic and manuscript regression tests |
| `papers/` | Article and complete lab paper, PDFs and editable sources |
| `lean/` | Original source-only Lean project and pinned dependencies |
| `research/` | Preserved numerical designs, selected outputs, code and checks |
| `docs/` | User guides, result-to-proof map and SHA-256 provenance |

This is a standalone release snapshot. See [citation information](CITATION.md)
and [licensing scope](NOTICE.md). Original software and Lean proofs are MIT;
that license does not relicense the manuscripts, third-party literature or dependencies.
