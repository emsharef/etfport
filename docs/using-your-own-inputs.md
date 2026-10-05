# Using your own inputs

The [README](../README.md#use-your-own-assumptions) contains a complete custom
allocation example. Its [runnable version](../examples/own_assumptions.py)
defines all inputs, solves the current allocation, adds future scenarios and
writes every policy's results to `my_result.json`. No paper preset or market
data service is required.

## Choose the input level

There are two ways to describe returns. Both produce the same `Moments` object
accepted by the optimizer.

| Starting point | What to supply |
|---|---|
| Forecasts for each instrument | `Moments(mean, covariance)`: a vector of next-quarter excess expected returns and the full predictive return covariance |
| A factor model and fund alpha estimates | `predictive_moments(...)`: factor exposures, premia, alphas, return-risk covariances, mean-estimation covariances and ETF fees |

For direct instrument forecasts, fees must already be reflected in `mean`.
That covariance must describe the uncertainty you intend the quarterly score
to penalize. A historical return covariance is not automatically the same as
a model's predictive covariance with uncertain means.

## Factor inputs and their dimensions

Let `N` be the number of funds, `M` the number of ETFs and `K` the number of
factors. The factor helper orders instruments as **all funds, then all ETFs**.
Use that same order for holdings, names, costs and every future state.

| Argument | Shape | Meaning |
|---|---|---|
| `fund_loadings` | N × K | Fund factor exposures; one fund per row |
| `etf_loadings` | M × K | ETF factor exposures; one ETF per row |
| `premium_mean` | K | Expected next-quarter factor excess returns |
| `alpha_mean` | N | Expected next-quarter fund alpha, net of internal expenses |
| `factor_covariance` | K × K | Factor return shocks conditional on the means |
| `fund_residual_covariance` | N × N | Fund residual return shocks conditional on the means |
| `etf_residual_covariance` | M × M | ETF tracking/residual return shocks |
| `premium_uncertainty` | K × K | Covariance of uncertainty about conditional factor means |
| `alpha_uncertainty` | N × N | Covariance of uncertainty about conditional fund alphas |
| `etf_fees` | M | Quarterly ETF fee/drag rates to subtract from ETF means |

Covariance entries are **not volatilities or correlations**. With standard
deviations `sd` and correlation matrix `corr`, construct
`covariance = np.outer(sd, sd) * corr`. The example's diagonal blocks assume
zero within-block correlations; replace them when your assumptions differ.
The covariance blocks must be positive semidefinite and the resulting
instrument covariance must be positive definite.

Under the helper's assumptions, the predictive covariance is the factor
loading matrix times `(factor_covariance + premium_uncertainty)` times its
transpose, plus the fund block
`fund_residual_covariance + alpha_uncertainty` and the ETF residual block.
This is a predictive-variance calculation, not an additional ambiguity penalty.
Do not count the same estimation uncertainty twice.

The helper assumes zero cross-covariance between its separate shock and
mean-error blocks. For example, it cannot express a premium–alpha error
cross-covariance or correlated fund–ETF residual shocks. If your model needs
those terms, construct the complete instrument-level `Moments` yourself.
Loadings are treated as known. Exposure uncertainty is not inferred by the API.

To include a factor that ETFs do not span, add its column to both loading
matrices, give the ETFs the exposures they actually have (possibly zero), and
expand all factor means and covariance matrices. Do not add that factor's
expected contribution to `alpha_mean` as well.

## Holdings, costs and risk preference

Normalize initial wealth to one for convenience. For an account of value `W`,
enter `holdings = dollar_positions / W` and `cash = dollar_cash / W`; multiply
output holdings, trades, cash and costs by `W` to recover dollar amounts.
Positions in future states remain amounts in that same initial wealth unit,
so they need not sum to one after returns have been realized.

`TradingCosts(buy=..., sell=...)` accepts a separate rate for each instrument
and trade direction. A value of `0.0005` charges 5 bp of the amount bought or
sold. Zero costs are allowed. These are investor trading costs; do not deduct
fund expenses already included in net alpha a second time. No cost ranking
between funds and ETFs is imposed.

`gamma` multiplies the quadratic risk term in the documented objective. The
example chooses 2.5 at initial wealth one; this is an assumption, not an
estimated preference. If you instead enter unnormalized dollars at wealth
`W`, use `gamma = 2.5 / W` to reproduce that allocation in dollars. Larger
gamma can increase cash; there is no constraint requiring all wealth to be
invested in risky instruments.

`caps` is optional. If supplied, it contains upper bounds in the same fixed
wealth unit, one per instrument; use `np.inf` for no cap. It does not impose
weights relative to future wealth. `fund_indices` contains the zero-based
positions to freeze for the ETF-only comparison; it does not restrict which
instruments the joint policies can trade. Set it explicitly for a meaningful
fund-versus-ETF comparison.

## Change today's beliefs without changing the starting portfolio

After running the README's first Python block:

```python
from dataclasses import replace
from etfport import solve_one_review

revised = replace(
    problem,
    moments=make_moments(premia=[0.010, 0.007], alphas=[0.001, 0.0005]),
)
revised_action = solve_one_review(revised).current
print(revised_action.trades)
```

This changes expected factor returns and retains the same holdings, costs,
uncertainty assumptions and gamma. Change the covariance inputs inside
`make_moments` when your uncertainty estimates also change. For a two-review
problem, update its scenario law and next-review moments as needed too:
replacing today's moments does not update the future distribution automatically.

## Specify future information for planning

Each `Scenario(probability, gross_returns, moments, label)` describes one
observable state at the next review. These fields describe different things:

- `gross_returns` marks today's holdings before the next trade. A gross return
  of `1.04` means an instrument holding grows by 4% over the intervening quarter,
  in the model's cash numeraire.
- `moments.mean` is the expected return over the **following** quarter, using
  the information available at that state. It is not the intervening realized
  return. `moments.covariance` is the following quarter's predictive covariance.
- `probability` is today's probability of reaching that state. Probabilities
  must be positive and sum to one; every instrument's gross return must be positive.

Construct these jointly from your return and information model. In particular,
today's score moments and the distribution of intervening returns should be
consistent. The API checks dimensions and probabilities, not economic
consistency or whether the supplied forecasts use future information.

The runnable tutorial chooses an eight-point finite return law with exactly
the specified current mean and covariance. Its forecast means then react to
observed ETF return surprises with an assumed coefficient of 0.25. Alpha
forecasts and covariance blocks stay fixed. This is an explicit illustrative
transition rule, **not** an estimated learning rule or an exact Bayesian update.
Matching moments does not determine tails or future trading opportunities;
another law with the same moments can give different planning decisions.
If you change the inputs, ensure the generated gross returns remain positive.

For your own planning model, replace the construction of `states` with your
observational states, their probabilities and their conditional next-quarter
forecasts. You may use a different next-quarter covariance in every state.
Distinct decisions require information that distinguishes those states; do not
give the optimizer separate decisions for hidden outcomes. The complete
[usage guide](using-the-package.md#supply-future-information-explicitly) states
the information contract and horizon limits.

## JSON input fields

Copy [custom_problem.json](../examples/custom_problem.json) and replace the
values. To run only today's optimization, omit `scenarios` and pass
`--horizon one`. `--horizon two` and `--horizon compare` require scenarios.

| Field | Required? | Contents |
|---|---|---|
| `holdings`, `cash` | Yes | Current instrument amounts and cash in a fixed wealth unit |
| `mean`, `covariance` | Yes | Current instrument-level predictive moments, net of fees |
| `buy_costs`, `sell_costs` | Yes | Investor trade rates in decimals, one per instrument |
| `gamma` | Yes | Positive quadratic risk coefficient in the chosen wealth unit |
| `names` | Optional | Unique readable instrument names in input order |
| `fund_indices` | Optional; set for ETF-only comparison | Zero-based indices of the fund positions |
| `caps` | Optional | Dollar/normalized-dollar caps; `null` means uncapped |
| `discount` | Optional | Discount on the next review's score, in (0, 1]; defaults to 1 |
| `scenarios` | Required for planning | List of objects with `probability`, `gross_returns`, `mean`, `covariance`, and optional `label` |

Keep every instrument vector the same length and every instrument covariance
square in that order. JSON does not accept factor-model inputs directly; use
the Python helper to construct predictive moments first if necessary.

The output file from `--horizon compare` contains `etf_only`, `one_review` and
`planning`. Each contains `current` and an ordered list `future`, along with
scores and diagnostics. Top-level `names` and `scenario_labels` identify the
ordering. Positive trades are purchases; negative trades are sales.
