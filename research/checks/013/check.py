"""Fixed M3 checks for claim 013. Numerical solves are not a proof.

Run with uv run python checks/013/check.py (repository uv.lock).
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
import math

import cvxpy as cp
import numpy as np


SIGNS = (-1, 1)
THETA = tuple(product(SIGNS, repeat=2))
SCENARIOS = tuple(product(SIGNS, repeat=2))
EPS = Q(1, 100)


def gross(theta, scenario, delta):
    regime, alpha_sign = theta
    sa, se = scenario
    return (1 + Q(regime, 2) + delta * (alpha_sign + sa),
            1 - Q(regime, 2) + delta * se)


def observation(theta, scenario, delta):
    ga, ge = gross(theta, scenario, delta)
    return (Q(theta[0], 2), -Q(theta[0], 2), ga - 1, ge - 1)


def bayes(delta):
    joint = defaultdict(lambda: defaultdict(Q))
    for theta, scenario in product(THETA, SCENARIOS):
        joint[observation(theta, scenario, delta)][theta] += Q(1, 16)
    masses = {y: sum(row.values()) for y, row in joint.items()}
    post = {y: {t: w / masses[y] for t, w in row.items()} for y, row in joint.items()}
    return masses, post


def trade(x, h, u, buy, sell):
    charge = sum(b * max(v, 0) + s * max(-v, 0) for v, b, s in zip(u, buy, sell))
    z, cash = tuple(v + dv for v, dv in zip(x, u)), h - sum(u) - charge
    assert min(*z, cash) >= 0
    return z, cash


def exact_checks(delta):
    masses, post = bayes(delta)
    assert len(masses) == 12 and sum(masses.values()) == 1
    ambiguous = [y for y in masses if len(post[y]) == 2]
    assert len(ambiguous) == 4 and sum(masses[y] for y in ambiguous) == Q(1, 2)
    for y in masses:
        assert (y[2] - y[0] == 0) == (y in ambiguous)
        if y in ambiguous:
            assert masses[y] == Q(1, 8) and set(post[y].values()) == {Q(1, 2)}
            assert {t[1] for t in post[y]} == {-1, 1}
        else:
            assert masses[y] == Q(1, 16) and list(post[y].values()) == [Q(1)]
    for theta in THETA:
        gs = [gross(theta, s, delta) for s in SCENARIOS]
        means = tuple(sum(g[i] for g in gs) / 4 for i in range(2))
        cov = tuple(tuple(sum((g[i] - means[i]) * (g[j] - means[j]) for g in gs) / 4
                          for j in range(2)) for i in range(2))
        assert cov == ((delta**2, 0), (0, delta**2))
        assert all(min(g) > 0 for g in gs)
    paths = tuple(product(THETA, SCENARIOS, SCENARIOS))
    moments = tuple(sum(gross(t, s0, delta)[i] * gross(t, s1, delta)[i]
                        for t, s0, s1 in paths) / len(paths) for i in range(2))
    assert moments == (Q(5, 4) + delta**2, Q(5, 4))
    assert tuple(sum(gross(t, s, delta)[i] for t, s in product(THETA, SCENARIOS)) / 16
                 for i in range(2)) == (1, 1)

    for ba, be, sa, se in product((Q(0), EPS), repeat=4):
        buy, sell = (ba, be), (sa, se)
        target = (Q(7, 15) / (1 + EPS), Q(8, 15) / (1 + EPS))
        z0, h0 = trade((Q(0), Q(0)), Q(1), target, buy, sell)
        for theta, s0, s1 in paths:
            g0, g1 = gross(theta, s0, delta), gross(theta, s1, delta)
            y = observation(theta, s0, delta)
            x1 = tuple(z * g for z, g in zip(z0, g0))
            # Uses only public factor sign, never alpha or the second draw.
            u = (Q(0), -x1[1]) if y[0] > 0 else (Q(0), Q(0))
            z1, h1 = trade(x1, h0, u, buy, sell)
            w = h1 + sum(z * g for z, g in zip(z1, g1))
            assert w >= Q(657, 505) - 6 * delta
            winner = 0 if y[0] > 0 else 1
            u = [Q(0), Q(0)]
            u[winner] = 1 / (1 + buy[winner])
            z1, h1 = trade((Q(0), Q(0)), Q(1), u, buy, sell)
            w = h1 + sum(z * g for z, g in zip(z1, g1))
            assert w >= (Q(3, 2) - 2 * delta) / (1 + EPS)
    print(f"delta={delta}: exact risk, Bayes and 16-corner pathwise funding checks passed")


def solve(root, future, delta):
    """Original M3 cash equations with one shared action per public observation."""
    masses, post = bayes(delta)
    u0 = cp.Variable(2)

    def cost(u):
        return 0.01 * cp.sum(cp.abs(u))  # all four rates at the box upper corner

    h0 = 1 - cp.sum(u0) - cost(u0)
    constraints = [u0 >= 0, h0 >= 0]
    if root == "E":
        constraints.append(u0[0] == 0)
    objective = 0
    for y in masses:
        # All histories yielding y share both this variable and this marked state.
        u1 = cp.Variable(2)
        x1 = cp.multiply(np.array([float(1 + y[2]), float(1 + y[3])]), u0)
        h1 = h0 - cp.sum(u1) - cost(u1)
        constraints.extend([x1 + u1 >= 0, h1 >= 0])
        if future == "E":
            constraints.append(u1[0] == 0)
        elif future == "N":
            constraints.append(u1 == 0)
        for theta, prob in post[y].items():
            for scenario in SCENARIOS:
                g = np.array(list(map(float, gross(theta, scenario, delta))))
                w = h1 + g @ (x1 + u1)
                objective += float(masses[y] * prob / 4) * cp.exp(-20 * (w - 1))
    problem = cp.Problem(cp.Minimize(objective), constraints)
    problem.solve(solver="CLARABEL", tol_gap_abs=1e-10, tol_gap_rel=1e-10,
                  tol_feas=1e-10, max_iter=500)
    assert problem.status == "optimal", problem.status
    return 1 - math.log(problem.value) / 20


def main():
    cap = Q(1, 1000)
    lower_e = Q(2129, 8080) - 9 * cap - cap**2
    upper_n = Q(1, 4) + cap**2
    upper_f = Q(3, 202) + Q(402, 101) * cap
    assert lower_e - upper_n == Q(226649, 50500000) > Q(1, 250)
    assert upper_f - lower_e == -Q(23801399, 101000000) < -Q(23, 100)
    assert 1 + Q(3, 4) + Q(3, 4)**2 / 2 == Q(65, 32) > 2
    for delta in (cap, Q(1, 2000)):
        exact_checks(delta)
    ce = {(d, r): solve(d, r, cap) for d in ("F", "E") for r in ("N", "E", "F")}
    gap = {r: ce["F", r] - ce["E", r] for r in ("N", "E", "F")}
    tol = 2e-6
    assert -tol <= gap["N"] <= float(upper_n) + tol
    assert gap["E"] > float(lower_e) - tol
    assert -tol <= gap["F"] <= float(upper_f) + tol
    assert gap["E"] - gap["N"] > 1 / 250 - tol
    assert gap["F"] - gap["E"] < -23 / 100 + tol
    print("Numerical gaps (absolute tolerance 2e-6):", gap)
    print("Claim 013 fixed checks passed; finite checks are not the uniform paper proof.")


if __name__ == "__main__":
    main()
