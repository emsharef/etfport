# harness_n: the M9 extension and its validation (preparation for D24; no findings)

PM's note 2026-09-30-d24-m9-prep, step 1. M9 is defined in model/SPEC.md on mathb/claim114-d24-target-move (eb786cb5;
not on main yet). It is M8 with M5's state equation, theta_{t+1} = Phi theta_t + (I - Phi) theta_bar + eta_{t+1}, with
eta centred and of covariance Q.

**What changed in harness_n.py**
- ModelN takes Phi, Q, theta_bar and a finite law for eta. mn_model takes phi, q (per coordinate of theta = (lambda,
  alpha)) and theta_bar, with eta two points per coordinate, +- sqrt(q).
- The filter updates with y_{t+1} and then predicts:
  - m_{t+1} = Phi (m_t + K_t nu_{t+1}) + (I - Phi) theta_bar;
  - P_{t+1} = Phi P^u_t Phi' + Q.
- The tree draws eta_1..eta_{T-2}, so theta moves along each path. With T = 2 (both reviews and the marking) only the
  filter at review 1 changes; eta first enters the law of y_2.
- The defaults (Phi = I, Q = 0, theta_bar = m_0) are M8: the code path is the one validate_n.py checks.

**Validation** (validate_m9.py writes validation_m9.json):

| check | result |
|---|---|
| (a) Phi = I, Q = 0 passed explicitly: experiment 054's 144 cells (dynamic and one-review roots) | 1.8e-12 and 0 |
| (a) the same against experiment 048's 72 cells (dynamic value and root) | 1.6e-17 and 2.2e-12 |
| (b) the filter against SPEC M9's scalar-block recursion at every review-1 node (Phi = diag(0.8, 0.6), Q = diag(4e-6, 2e-6), theta_bar != m_0; both regimes) | m_1 to 5e-18, P_1 to 3e-21 |
| (c) finite law, enumerating (theta_0, z_1, eta_1): P_1 is the error covariance of theta_1 given y_1; E m_1 = Phi m_0 + (I - Phi) theta_bar | 1e-20 and 5e-18 |
| (d) T = 3 tree: the law of y_2 has mean G (Phi m_0 + (I - Phi) theta_bar) + d and covariance G (Phi P_0 Phi' + Q) G' + R | 2e-17 and 1e-17 |

validate_n.py reruns unchanged: 048 and 054 to 2e-12, incumbent duals against finite differences to 8e-12.

**Scope.** This is preparation only. Experiment 057 (claim 114's formula check) is registered only once claim 114 is on
main.
