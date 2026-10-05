"""Fixed checks for claim 012 (M3); numerical optimization is not its proof.

Run: uv run python checks/012/check.py
Environment: repository pyproject.toml and uv.lock. No randomness or external data.
"""

from fractions import Fraction as Q
from itertools import product
import math

import cvxpy as cp
import numpy as np


EPS = Q(1, 100)
RETURNS = ((Q(3, 2), Q(1, 2)), (Q(1, 2), Q(3, 2)))
LOWER_E = Q(507, 2020)
UPPER_F = Q(3, 202)


def cost(u, buy, sell):
    return sum(b * max(v, 0) + s * max(-v, 0)
               for v, b, s in zip(u, buy, sell))


def trade(x, h, u, buy, sell):
    z = tuple(a + b for a, b in zip(x, u))
    c = h - sum(u) - cost(u, buy, sell)
    assert min(*z, c) >= 0
    return z, c


def exact_checks():
    assert LOWER_E - Q(1, 4) == Q(1, 1010)
    assert UPPER_F - LOWER_E == -Q(477, 2020)
    assert Q(657, 505) - Q(21, 20) == LOWER_E
    assert Q(3, 2) - Q(150, 101) == UPPER_F
    # First-quarter public returns distinguish the two fixed parameters.
    assert RETURNS[0] != RETURNS[1]
    rates = list(product((Q(0), EPS), repeat=4))
    rates.append((Q(1, 400), Q(3, 400), Q(1, 200), Q(1, 1000)))
    for ba, be, sa, se in rates:
        buy, sell = (ba, be), (sa, se)
        a, p = Q(7, 15) / (1 + EPS), Q(8, 15) / (1 + EPS)
        z0, h0 = trade((Q(0), Q(0)), Q(1), (a, p), buy, sell)
        for state, gross in enumerate(RETURNS):
            x1 = tuple(x * g for x, g in zip(z0, gross))
            u1 = (Q(0), -x1[1]) if state == 0 else (Q(0), Q(0))
            assert u1[0] == 0  # continuation E
            z1, h1 = trade(x1, h0, u1, buy, sell)
            w = h1 + sum(x * g for x, g in zip(z1, gross))
            assert w >= Q(657, 505)
            # Root cash, then purchase the observed winner under continuation F.
            winner = state
            u = [Q(0), Q(0)]
            u[winner] = 1 / (1 + buy[winner])
            z, h = trade((Q(0), Q(0)), Q(1), u, buy, sell)
            assert h == 0
            assert h + sum(x * g for x, g in zip(z, gross)) >= Q(150, 101)
    # Zero-fee policy payoffs, without solver tolerances.
    for state, gross in enumerate(RETURNS):
        assert sum(Q(1, 2) * g * g for g in gross) == Q(5, 4)
        a, p = Q(7, 15), Q(8, 15)
        w = a * gross[0] ** 2 + p * gross[1] * (
            Q(1) if state == 0 else gross[1])
        assert w == Q(79, 60)
    assert math.exp(10) > 1.5 and math.log(2) < 1
    print(f"Exact funding and payoff checks: {len(rates)} rate points passed")


def solve(root, future, rates):
    """Optimize original trade/cash equations, independently of paper bounds."""
    ba, be, sa, se = map(float, rates)
    buy, sell = np.array([ba, be]), np.array([sa, se])

    def fees(u):
        return buy @ cp.pos(u) + sell @ cp.pos(-u)

    u0 = cp.Variable(2)
    cash0 = 1 - cp.sum(u0) - fees(u0)
    constraints = [u0 >= 0, cash0 >= 0]
    if root == "E":
        constraints.append(u0[0] == 0)
    objective = 0
    for gross_q in RETURNS:
        gross = np.array(list(map(float, gross_q)))
        incoming = cp.multiply(gross, u0)
        u1 = cp.Variable(2)
        cash1 = cash0 - cp.sum(u1) - fees(u1)
        constraints.extend([incoming + u1 >= 0, cash1 >= 0])
        if future == "E":
            constraints.append(u1[0] == 0)
        elif future == "N":
            constraints.append(u1 == 0)
        w = cash1 + gross @ (incoming + u1)
        # Common shift keeps exp-cone objective numerically well scaled.
        objective += 0.5 * cp.exp(-20 * (w - 1))
    prob = cp.Problem(cp.Minimize(objective), constraints)
    prob.solve(solver="CLARABEL", tol_gap_abs=1e-10, tol_gap_rel=1e-10,
               tol_feas=1e-10, max_iter=500)
    assert prob.status == "optimal", prob.status
    return 1 - math.log(prob.value) / 20


def numerical_checks():
    cases = {
        "zero fees": (0, 0, 0, 0),
        "asymmetric positive fees": (Q(1, 400), Q(3, 400), Q(1, 200), Q(1, 1000)),
    }
    for name, rates in cases.items():
        ce = {(d, r): solve(d, r, rates) for d in ("F", "E") for r in ("N", "E", "F")}
        gaps = {r: ce["F", r] - ce["E", r] for r in ("N", "E", "F")}
        tol = 2e-6
        assert -tol <= gaps["N"] <= 0.25 + tol
        assert gaps["E"] > float(LOWER_E) - tol
        assert -tol <= gaps["F"] <= float(UPPER_F) + tol
        assert gaps["E"] - gaps["N"] > float(Q(1, 1010)) - tol
        assert gaps["F"] - gaps["E"] < -float(Q(477, 2020)) + tol
        assert ce["F", "E"] >= float(Q(657, 505)) - tol
        assert ce["E", "E"] < 1.05 + tol
        if name == "zero fees":
            assert abs(ce["F", "N"] - 1.25) < tol
            assert abs(ce["F", "F"] - 1.5) < tol
            assert abs(ce["E", "F"] - 1.5) < tol
            exact_ee = 1 + (math.log(2) - math.log1p(math.exp(-10))) / 20
            assert abs(ce["E", "E"] - exact_ee) < tol
        print(name, "(numerical, absolute tolerance 2e-6):",
              "; ".join(f"Delta_{r}={gaps[r]:.9f}" for r in ("N", "E", "F")))
    print("All fixed claim 012 checks passed; numerical checks are not a proof.")


if __name__ == "__main__":
    exact_checks()
    numerical_checks()
