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

## Install and run

Python 3.12 or newer:

```sh
python -m pip install "git+https://github.com/emsharef/etfport.git"
etfport example --scenario premium_down_persistent --output result.json
```

This reproduces the article's assumed downward-equity/upward-duration revision
from an allocation optimized under the old beliefs. The command reports current
trades and separately reports the current benefit from fund trading and the
incremental two-review planning benefit. Other examples include `unchanged`,
`alpha_up`, `alpha_down`, `style_up`, and `style_down`.

For development or to read and reproduce the papers:

```sh
git clone https://github.com/emsharef/etfport.git
cd etfport
python -m venv .venv
. .venv/bin/activate
python -m pip install -e ".[dev,research]"
pytest
python scripts/check_package.py
```

## Python API

```python
from etfport import compare_policies
from etfport.examples import make_example

problem = make_example("alpha_up")  # assumed inputs from the article
comparison = compare_policies(problem)
print(comparison.planning.current.trades)
print(comparison.current_fund_benefit_bp)
print(comparison.planning_gain_bp)
```

For your own forecasts, construct `AllocationProblem` from `Moments`,
`Portfolio`, `TradingCosts` and an optional finite set of `Scenario` objects.
Use `predictive_moments` to construct moments from factor loadings, alpha,
fees, return covariance and mean-estimation covariance. Alternatively:

```sh
etfport solve examples/custom_problem.json --horizon compare --output result.json
```

The [usage guide](docs/using-the-package.md) specifies units, funding,
scenario information, solver diagnostics and interpretation. The
[model and scope guide](docs/model-and-scope.md) explains what the software
implements and how that differs from the scope of the formal theorems.

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
