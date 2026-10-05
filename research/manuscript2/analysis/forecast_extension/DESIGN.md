# Other forecast revisions and an unspanned factor

Saved before computation, 2026-10-02. Model version M9. User-authorized extension for the manuscript revision, using existing finite funded solvers. All inputs are assumptions. This is not empirical estimation, a new theorem, or a search for large planning gains.

## Question and design

Retain the six-fund, three-ETF menu, old-optimal starting-portfolio construction, observation convention and funded policy comparison from ../forecast_revision/DESIGN.md. Gamma is 2.5; fund costs 5 bp and ETF costs 2 bp per purchase or sale; no caps. Initial wealth is one. Old portfolio acquisition costs are sunk. Solve the old static optimum before applying news, and verify no one-review trade under unchanged beliefs. The control need not be a stationary dynamic portfolio.

Seven scenarios use the original three-factor menu: unchanged beliefs; persistent duration-premium revisions of +/-10 bp per quarter, holding the equity and credit sleeve premia fixed; persistent credit-premium revisions of +/-15 bp with the other sleeve premia fixed; and persistent Credit A alpha revisions of +/-5 bp with every other mean fixed. Convert sleeve-premium revisions through the inverse ETF loading matrix, as before.

Add a fourth independent economic factor for the other 42 cases. Call it a style factor: it is an observed attribution factor, not an admissible standalone investment. Its old quarterly premium is zero; return-shock SD is 3%; premium prior SD is 20 bp at baseline and 10 or 40 bp in sensitivities; state-noise SD is 5 bp. Fund loadings on it, in the existing order, are (0.5,-0.5,0,0,0.4,-0.4); all three ETFs have zero loading. Opposite style loadings do not imply short investor positions. Keep all existing alpha definitions, alpha means, alpha uncertainty, other loadings and other risks unchanged. Recompute each old optimum with the additional factor's risk and the specified old beliefs; do not reuse the old three-factor optimum as a deliberately misallocated starting portfolio.

For each of the three prior SDs, revise the style premium by -40,-20,-10,0,+10,+20,+40 bp. Cross with persistent forecasts (long-run mean equals revised current mean) and reverting forecasts (long-run mean stays zero, so next-review expected revision is 80% of today's). The two zero-revision cases duplicate the same control intentionally. Total 7 + 3*7*2 = 49 cases. Mean uncertainty and realized-return risk remain separate. This is a conditional revision exercise, not a historical signal experiment.

## Comparisons and reporting

Compare the ETF-only one-review policy, the joint one-review policy, and the funded two-review optimum. All policies use the same future information and full funded continuation. Report instrument trades, capital allocated to funds/ETFs/cash, each factor exposure, the current score benefit from allowing fund trades, the incremental planning gain, and the unchanged-beliefs controls. The main figure shows style exposure as a function of the revised premium, for ETF-only, joint one-review and planning, with a separate panel comparing persistence. It must show the zero-change control and both signs; no smoothing or fitted threshold claim.

For an ETF-only current trade, the additional-factor exposure is fixed algebraically because all ETF loadings on that factor are zero. Its current-premium revision adds a constant to the ETF-only objective while moments, bounds and incumbents stay fixed. Check numerically that ETF-only root holdings do not change across the revision grid at a fixed prior SD. The joint optimum is allowed to remain inside a hold region; missing span does not force a trade after every update. Do not apply the unconstrained quadratic Schur-complement policy formula as if it solved this funded proportional-cost problem.

Use the existing axis law: 432 states for the original menu and 520 for the four-factor menu (20 parameter atoms times 26 shock atoms). Public factor and instrument observations are independent of ownership. The linear filter is not the finite-law exact posterior. No borrowing at either review; positive gross returns throughout. Save all cases and numerical warnings. Independently reconstruct moments, state atoms and the diagonal filter, then solve vectorized QPs for the seven original-menu scenarios and the fourteen baseline-SD style scenarios. Check old static solutions independently with SLSQP; check budgets within 2e-7, reconstructed objectives within 1e-8, independent policy values within 1e-5 bp and holdings within 1e-5 of initial wealth. No Monte Carlo uncertainty arises from the exact finite-law sums.

## Deviations

None at design save.

The first sweep stopped when a joint solver returned optimal_inaccurate under its 1e-12 absolute-gap setting. Preserve partial output as initial_attempt.jsonl. For such a status, retry the same problem with 1e-10 absolute gap, 1e-10 relative gap and feasibility tolerance, and at most 1000 iterations. Record both statuses and keep all original warnings. The original registered objective, funding and independent-agreement thresholds remain unchanged. No economic inputs or scenarios change. Extend independent checks to every case with a retry or warning, including prior-SD sensitivity cases if needed.

The independent QP also returned optimal_inaccurate at its strict stopping settings on the first four-factor case. Use 1e-9 absolute/relative gap and 1e-10 feasibility tolerance for that independent implementation; its objective is measured in bp. Retain all registered comparison thresholds. This changes numerical termination only.

Case 28 (style premium -40 bp, reverting, prior SD 20 bp) also failed the first retry's termination criterion. Add a final retry at absolute gap 1e-8, relative gap 1e-9 and feasibility 1e-9, retaining the original registered independent-agreement and accounting checks. Preserve the second partial sweep as second_attempt.jsonl.

Independent reproduction was expanded to all 49 cases. At prior SD 40 bp, the SLSQP old portfolio's small holding error caused a 0.000026 bp value disagreement, above the registered threshold. Polish that independent old static solution with its active-set linear KKT equations and check every inactive inequality, then reproduce the policies. This improves the independently constructed incumbent rather than relaxing the comparison tolerance or changing an economic input.
