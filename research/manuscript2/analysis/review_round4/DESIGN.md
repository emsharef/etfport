# Fourth-round review: interpretation and numerical diagnostics

Saved before additional calculations, 2026-10-02. Model version: M9. This is a reanalysis of the existing 108- and 49-case designs, not a new calibration, horizon study or theorem. The user requested substantive treatment of the fourth referee report and challenged the meaning of the assumed numerical magnitudes.

## Questions and design

1. Extract full instrument trades, current fund-trading benefits, two-review planning gains and transaction costs for every existing case. Check gains independently from saved objective components; retain both denominators and horizons explicitly. Summarize the two deliberately selected grids separately, including controls. No statistical-population interpretation of their medians.
2. Report the selected table rows, both premium-rotation directions, and all nine cases of the existing all-negative-old-alpha configuration. Compute fee credits from the published loading and fee matrices. Do not attribute the fund allocation entirely to fees or extrapolate the configuration to observed fund populations.
3. Recover cash-constraint duals for the three baseline Figure 2 cases only (persistent downward-equity/upward-duration revision, Equity A alpha +5 bp, Equity A alpha -5 bp). Use the existing independent direct-tree construction and vectorized QP formulation, with identical economic inputs. Solve both the joint two-review program and the repeated-one-review continuation. Report root cash, root budget multiplier, effective dynamic cash multiplier, next-review conditional multiplier minimum/mean/maximum and probability exceeding 1e-7. Normalize QP duals for the objective's 1e4 scaling and next-review probabilities. Distinguish numerical positivity, possible multiplier nonuniqueness, and a joint root multiplier from the root of a policy with holdings fixed. For the myopic policy report its separately optimized one-review root multiplier, not the arbitrary root multiplier in the fixed-holdings continuation program.
4. Check reconstructed solutions against existing results: root holdings within 1e-5 of wealth and objective/gain within 1e-5 bp. Retain warnings. This recovers omitted diagnostics; it does not causally decompose the planning benefit or transfer the one-fund theorem to the many-fund application.

## Scope

No new parameter cells, horizon sweep, fee ablation, new posterior or replacement objective. A simple frozen-allocation accounting example may explain horizon amortization, but is explicitly not a theorem for the adaptive funded model. No universal no-pretrade conclusion is drawn from linear costs. No public archival deposit is claimed.

## Deviations

None at design save.
