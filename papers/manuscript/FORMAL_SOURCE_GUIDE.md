# Formal-verification supplement

This supplement supplies source locations for the results of *When Forecasts Change: Rebalancing Active Funds and ETFs*. The article states mathematical assumptions and verification limits in Appendix A; the locators below are for reproducing the formal checks.

Lean toolchain: `leanprover/lean4:v4.35.0-rc2`. Mathlib revision: `6ebcdee77a1b7bf10f211d4c993d85fbb19644bc`.

`formal-source.zip` contains the Lean statements, proof modules, explicit hypotheses for cited mathematics and dependency pins. Its `SOURCE_MANIFEST.json` records the repository revision and SHA-256 hashes. `FORMAL_STATEMENTS.txt` gives exact common-multiplier and two-review declarations with a notation guide. The external mathematical hypotheses remain hypotheses; the numerical policies are not machine checked.

A permanent public archive and DOI have not been deposited. The local bundle is a review artifact, not fulfillment of the outstanding archival condition for publication.

| Article result | Statement file in `lean/Standalone/` | Declarations / scope |
|---|---|---|
| Proposition 1; Corollary 2 | `M7FundHoldBuySellCriterion.lean` | `SpanningRule`, `Criterion`, `EtfTest` |
| Proposition 3 | `M7OneEtfTwoScalars.lean` | `One`, `OnePrice`, ETF regimes and cash monotonicity |
| Proposition 4 | `M7IncumbentAwareFirstStage.lean` | `FibreMult`, `LossBounds`, `Exactness` |
| Proposition 5 | `M5PartialAdjustmentSplit.lean` | `LQ`, `BellmanVerif`, `Aim`, `Separation` |
| Equation (19), learning bound | `M5LearningAimTwoSpeeds.lean`, `M5WhenAnticipationMatters.lean`, `IntegrationTheorem.lean` | Scalar learning and anticipation bounds; `AnticipationOrder` |
| Equation (20), quadratic gap | `M5PlugInValueLoss.lean` | `OneStep`, `Pathwise`, `Stability`; expected telescoping is a paper proof |
| Proposition 6 | `M7DynamicBundlingBand.lean`, `M7DynamicBundlingShape.lean` | `EffectiveBand`, `ResidualCeiling`, `Frictionless`, `Edges`, `Monotone2` |
| Corollaries 7–8 | `M7TwoReviewsBindingBudget.lean` | `Tomorrow`, `Root`, `MyopicTest`, costless specialization |
| Equations (25)–(26) and interior-trade implications | `M7TwoReviewsBounds.lean` | `CashPriceBound`, `SlackWhenCovered`, `DynamicCashPrice`, `Brackets`, `InteriorTrade`, `InteriorTradeBinding` |
| Unspanned reduction, Appendix B.2 | `M5MissingDirectionLeak.lean` | Hedged-premium and residual-risk identities |
| Finite learning example, Appendix E.1 | `M8WorkedLearningExample.lean` | Filter/current moment identities; numerical policy comparison is not formalized |

Proof modules are in `lean/Novel/`; external hypotheses are in `lean/Upstream/`. With the pinned dependencies installed, unpack the source archive, enter `lean/`, and run `lake build Audit`. The Mathlib compiled cache is not bundled; restoring dependencies requires network access.
