# Release validation

Local checks completed for version 0.1.0 on 2026-10-05, using Python 3.13.6
and the direct dependency versions in `requirements-tested.txt`:

| Check | Outcome |
|---|---|
| `pytest` | 36 tests passed, including 11 manuscript scenarios through the public API |
| `python scripts/check_package.py` | Preserved source hashes, guide links, both PDFs and accounting identities for all 157 saved forecast cases passed |
| `python scripts/reproduce.py verify` | Nine baseline and all 49 extension cases independently re-solved and compared; three budget diagnostics rerun |
| `python scripts/reproduce.py figures` | Article illustrations regenerated from the included numerical outputs |
| `python scripts/reproduce.py papers` | Both LaTeX papers compiled with Tectonic; the lab paper retains its existing layout warnings |
| `python -m build --no-isolation` | Wheel and source distribution built; test fixture included in source distribution |
| Isolated wheel installation | Installed in a separate virtual environment and ran the unspanned-style example from outside the repository |
| `lake build Audit` | Passed on the source-identical laboratory Lean tree: 6,559 declarations checked |

The Lean check used the existing pinned dependency cache. Every distributed
Lean source file is matched to that tree by SHA-256; a second fresh dependency
download was not performed. The full 157-case original optimization sweep was
not rerun for this release. The independent subset above was rerun, and all
157 saved cases passed the release accounting checks.

GitHub Actions checks the package on Python 3.12 and 3.13 on each push.
Its separate Lean job is manually selectable. See the repository's Actions
tab for remote run results.

These checks establish reproducibility and numerical consistency for the
tested cases. They do not establish an empirical calibration, formally verify
the Python implementation, or extend the mathematical theorems' scope.
