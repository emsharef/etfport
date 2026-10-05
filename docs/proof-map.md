# Article results and Lean sources

This map uses the article's numbering after the fourth review. Read the
statement hypotheses and Appendix A before applying a result. The Python API
solves finite programs numerically; the table does not certify that code.

| Article statement | Exact Lean statement source | Verified scope |
|---|---|---|
| Proposition 1; Corollary 2 | [FundHoldBuySellCriterion](../lean/Standalone/M7FundHoldBuySellCriterion.lean) | Spanning rule; common-multiplier ETF test; necessity conditional on cited optimality |
| Proposition 3 | [OneEtfTwoScalars](../lean/Standalone/M7OneEtfTwoScalars.lean) | Scalar responses and root properties; the paper identifies the remaining existence/coordinate steps |
| Proposition 4 | [IncumbentAwareFirstStage](../lean/Standalone/M7IncumbentAwareFirstStage.lean) | Exposure-first loss bound and sufficient exactness; converse conditional |
| Proposition 5 | [PartialAdjustmentSplit](../lean/Standalone/M5PartialAdjustmentSplit.lean) | Riccati, aim and abstract Bellman identities; statistical/full-policy boundary disclosed |
| Equation (19), learning bound | [LearningAimTwoSpeeds](../lean/Standalone/M5LearningAimTwoSpeeds.lean), [WhenAnticipationMatters](../lean/Standalone/M5WhenAnticipationMatters.lean), [IntegrationTheorem](../lean/Standalone/IntegrationTheorem.lean) | Constant-state scalar learning/anticipation bounds |
| Equation (20), quadratic gap | [PlugInValueLoss](../lean/Standalone/M5PlugInValueLoss.lean) | One-step completed square; expected telescoping is a paper proof |
| Proposition 6 | [DynamicBundlingBand](../lean/Standalone/M7DynamicBundlingBand.lean), [DynamicBundlingShape](../lean/Standalone/M7DynamicBundlingShape.lean) | Hold band and residual-width ceiling; monotonicity conditional on the cited lattice input |
| Corollaries 7–8 | [TwoReviewsBindingBudget](../lean/Standalone/M7TwoReviewsBindingBudget.lean) | One-fund/one-ETF funded joint conditions and myopic test, with explicit optimality hypothesis |
| Funding bounds | [TwoReviewsBounds](../lean/Standalone/M7TwoReviewsBounds.lean) | Statewise cash-price existence and selection limitations |
| Unspanned reduction | [MissingDirectionLeak](../lean/Standalone/M5MissingDirectionLeak.lean) | Unconstrained hedged-premium and residual-risk identities |
| Appendix E learning example | [WorkedLearningExample](../lean/Standalone/M8WorkedLearningExample.lean) | Finite-law moment identities; numerical policies are outside Lean |

The [source/declaration supplement](../papers/manuscript/FORMAL_SOURCE_GUIDE.md)
provides declaration names. Proof modules retain the corresponding names in
`lean/Novel/`. The article's full mathematical proofs are in Appendix D.
