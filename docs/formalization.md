# Formal verification

The [proof map](proof-map.md) links the edited article's numbered results to
Lean statements. The broader [fidelity record](archive/FIDELITY.md) and
[lab proof map](archive/LAB_PROOFMAP.md) retain the full research scope.

```sh
cd lean
lake exe cache get
lake build Audit
```

Lean is pinned to 4.35.0-rc2, Mathlib to
`6ebcdee77a1b7bf10f211d4c993d85fbb19644bc`, and transitive dependencies are
pinned by `lake-manifest.json`. Install the elan toolchain manager first.
The initial build downloads dependencies and needs several gigabytes of disk
space. The release includes sources, not `.lake` caches.

`Standalone` contains readable statements, `Novel` their proofs and supporting
lemmas, and `Upstream` explicit hypotheses for cited external mathematics.
`Audit.lean` checks the allowed axiom dependencies. The internal Lake package
name `lab` is retained to preserve the original configuration.

A Lean proof establishes its encoded proposition under the hypotheses in its
type. The polyhedral optimality and lattice-theoretic inputs are explicit
hypotheses where the article says so; they are not newly reconstructed general
theorems. Gaussian interpretations, selected policy verification arguments and
expectation/telescoping steps have the paper-only scope disclosed in Appendix A.
The [axiom ledger](archive/AXIOMS.md) documents upstream assumptions and instances.

Neither the new public Python API nor the historical numerical solvers are
machine-checked implementations. The package validates them numerically,
including independent formulations, but does not claim verified floating-point
optimization or theorem extraction into executable Python.

The paper's local formal snapshot and exact excerpts remain available in
`papers/manuscript/`. The public GitHub source release provides versioned access;
a permanent public archive with a DOI remains an outstanding publication step.
