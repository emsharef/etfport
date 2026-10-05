# Mathematical and software scope

The primary Python API implements the funded finite-dimensional programs in
manuscript Sections 2–4: a concave quarterly quadratic score, directional
proportional costs, long-only positions, optional dollar caps and nonnegative
cash. Its two-review solver includes return marking and nonanticipative
state-contingent continuation. An expected sum of quarterly scores is an
explicit mandate; it is not a solution to a terminal-wealth utility problem.

`predictive_moments` implements Equation (2): known factor loadings, factor
return risk, separate premium/alpha estimation uncertainty, fund residual risk,
ETF tracking risk and fees. Cross-block residual/mean-error covariances are
assumed zero in that helper. Supply `Moments` directly for a different positive
definite score covariance. No extra ambiguity-aversion penalty is added.

The Python solver handles arbitrary instrument counts and finite next-review
states. It directly solves a convex program; it does not claim a new general
closed-form many-fund dynamic theorem. The formal two-review characterization
in the article has one fund and one ETF and additional stated hypotheses.
The code is tested numerical implementation, not extracted or verified Lean code.

The API does not estimate alpha or factor premia from a historical fund sample,
choose an empirical prior, support taxes or fixed transaction fees, or send
orders to a broker. It does not implement an infinite-horizon policy or infer
a stable portfolio attractor. A generic longer-horizon experimental harness
is preserved in the research archive, but is not the supported public API.

The built-in examples reproduce the article's 432-state or 520-state finite
axis laws and linear filter. The filter is a linear predictor, generally not
the exact posterior of that finite law. Conditional forecast revisions are
assumed scenarios, not outputs of an estimated signal process. The old optimal
portfolio is a controlled initial condition with acquisition costs sunk, not
an asserted infinite-horizon optimum.

The numerical illustrations retain the article's limitations: fund allocation
depends materially on assumed alpha, ETF fee savings and residual diversification;
planning value depends on the horizon and forecast evolution. Small planning
gains in those cases do not establish a universal small-gain result, and large
portfolio differences do not establish economically material performance gains.
