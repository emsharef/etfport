# Reproducing the results

Install from the repository root:

```sh
python -m pip install -e ".[dev,research]"
pytest
python scripts/check_package.py
python scripts/reproduce.py examples
```

The public-API tests reproduce all nine baseline forecast revisions and the
positive/negative unspanned-style revisions against independently checked saved
results. Other tests check a closed-form scalar optimum, asymmetric hold costs,
mandatory sales, no-leverage cash accounting, wealth-unit scaling, conditional
dual normalization and invalid inputs. They do not establish empirical validity.

`examples` writes fresh result JSON to `build/examples/`. To regenerate the
article's five illustrations from saved results:

```sh
python scripts/reproduce.py figures
```

Plots are written under `research/manuscript2/figures/`; the published figures
in `papers/manuscript/figures/` remain preserved. Main figures use the current
forecast-revision files. Earlier arbitrary-start figures are not included as
article figures.

## Re-solve the numerical studies

```sh
python scripts/reproduce.py verify
python scripts/reproduce.py analysis
```

`verify` runs the existing independent checks and the three budget diagnostics.
`analysis` recomputes the 108- and 49-case designs, then runs the checks and
reports. These commands can take considerably longer than the API tests. They
write outputs in the research directories; use a fresh clone if retaining the
original generated files matters. The experimental designs and recorded solver
deviations remain in each directory. Recalculation does not overwrite the papers.

The exact saved laboratory dependency resolution is in `research/uv.lock`, with
its original `research/pyproject.toml`. It contains optional packages beyond the
public API. To recreate that environment with uv, run `uv sync --locked` in
`research/`. The root public-package dependencies are intentionally smaller;
`requirements-tested.txt` records the direct numerical/test versions used for
this release. Different supported solver versions may change final digits.

The original authors' solver and the independent vectorized programs are both
included. The 157 cases use assumed finite probability laws with exact finite
sums, so they have no Monte Carlo seed or Monte Carlo standard error. This is
not an empirical backtest or a claim that the linear filter is an exact posterior.

## Build the papers

With Tectonic installed:

```sh
python scripts/reproduce.py papers
```

This builds `build/papers/manuscript/main.pdf` and
`build/papers/lab/main.pdf` from the included LaTeX and bibliographies.
Tectonic may need network access to obtain TeX support files. The Markdown
sources are also included, but no lab scheduler or Markdown converter is
required for these portable PDF builds. The preserved lab paper has its
original long lines and layout warnings; it is a research record, not the
edited article.

## Check Lean

See the [formalization guide](formalization.md). A full Lean build is separate
from running Python. The root numerical CI runs on Python 3.12 and 3.13;
Lean checking can also be requested through the workflow's manual input.

## Provenance

[The source manifest](source-snapshot.json) records the laboratory revision,
source-to-release paths and individual SHA-256 hashes. The edited manuscript
was not tracked at that laboratory revision, so its file hashes are the
provenance for that component. Source code and statements are preserved byte
for byte. Generated numerical outputs may differ within documented tolerances
after a rerun. No publication history or DOI is inferred from the snapshot.
