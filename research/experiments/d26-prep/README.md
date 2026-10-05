# D26 preparation: the integrated example, the three policies, the bound terms and the scale limit

PM's note 2026-10-01-d26-start, step 1. This is preparation: there are no findings and no registered cases. The
registered experiment (058) imports this code. Its sensitivity design is registered after math's and mathb's definition
notes for policy 2 and the bound terms arrive.

## The model and the example (spec.py; every number is an assumed input)
- **M9** (model/SPEC.md) with several funds and ETFs. harness_n.py is extended for D26 and validated in
  validate_d26.py and validation_d26.json.
- **The example:** two factors, two ETFs (a broad one and a tilted one, with fees and small tracking residuals), three
  funds with distinct footprints, cash, purchase and sale rates from the equity-style or fixed-income-style preset, fund
  caps, no shorting, and the funded budget at both reviews.
- **Kept distinct:**
  - realized-return risk (the shocks z, Sigma_r);
  - uncertainty about the conditional means (the filter's P_t);
  - the state's own evolution (Phi, Q, theta_bar).
- **What the manager observes.** The factor returns and every instrument's return, y = (f, r^A, r^E). The filter is M9's
  Kalman recursion. Under the finite law it is the best linear estimate, not the exact posterior; under the Gaussian
  law it would be the posterior. With independent residuals and a zero prior cross-covariance, the premium and alpha
  blocks decouple, and P_t stays diagonal (checked).
- **Scope of the funding bounds.** Sigma_0 and Sigma_1 must be entrywise nonnegative, which holds at the example's
  inputs (spec.entrywise_nonnegative). Cases outside it will be labelled.

## The policies and the bound terms (policies.py)
- **Policy 1, repeated one-review:** today's one-review optimum, then tomorrow's funded one-review optimum at every
  state.
- **Policy 2, the plan without tomorrow's budget:** today's root of the two-review program with tomorrow's budgets
  dropped and today's kept, then funded one-review optimal trades tomorrow (no free financing).
- **Policy 3:** the full funded two-review optimum.

Each is valued by J(x): today's score plus beta times tomorrow's funded optimum. Losses are V^dyn - J(x), in bp of
initial wealth.

**Bound terms** (terms of upper bounds, not a decomposition of the loss):
- claim 049's band term at the myopic root (minimized over the admissible incumbent-value box);
- claim 115's root-residual band term at any holding (a small QP);
- the tail term beta E[eta_bar D], the uncovered fraction eps, and 049's input-only line;
- 115's planned purchase PP and its innovation-driven part Delta.

Consistency on a smoke instance outside any design: J at the dynamic root equals V^dyn (2e-13); 115's band term
vanishes at policy 2's root (7e-20), as the claim states.

## The scenario representation and its limit (scale.py, scale.json)
- **The product law** (two points per coordinate, the lab's reference) has 2^(K+N) parameter atoms times 2^(K+N+M)
  shock atoms. The example already has 4,096 states, and the count doubles twice per added fund.
- **The axis law** (`law="axis"`, 2d atoms of +- sqrt(d) sd per coordinate) has the same means and covariances, with
  2(K+N) times 2(K+N+M) states. It is a finite law, as M7's finite-law variant requires, but a coarser one: its atoms
  are larger, and its higher moments differ from the product law's.
- scale.py measures both laws up to tens of funds: states, variables, solver status and iterations, runtime, peak
  memory, and a feasibility check. The results are in scale.json, and the limits are stated there.
