"""Independent fixed-witness check of reported experiment 008, M3.

Rebuild fixture A from its primitives. Optimize post-trade holdings/cash with
linear cost-piece resource constraints and a log-sum-exp objective. No experiment
solver, Bayes helper or fixture object is imported. Free disposal in the resource
formulation does not change the optimum: increasing retained cash to saturate
each budget preserves controls and improves every affected terminal payoff.

Replay the returned holdings as actual funded trades. Solver/replay agreement is
a numerical diagnostic, NOT a certified optimum error bound. uv run python
checks/exp008-witness/check.py; environment pinned by repository uv.lock.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path

import cvxpy as cp
import numpy as np
from scipy.special import logsumexp


THETA = tuple(product((Q(1, 100), Q(1, 25)), (Q(-1, 100), Q(1, 50))))
SHOCKS = tuple(tuple(sign * size for sign, size in zip(signs,
               (Q(9, 100), Q(2, 25), Q(3, 200), Q(1, 100))))
               for signs in product((-1, 1), repeat=4))


def observation(theta, shock):
    premium, alpha = theta
    f1, f2 = premium + shock[0], Q(1, 100) + shock[1]
    ga = 1 + Q(23, 25) * f1 + Q(31, 50) * f2 + alpha + shock[2]
    ge = 1 + f1 - Q(3, 10000) + shock[3]
    assert min(ga, ge) > 0
    return f1, f2, ga, ge


def tree():
    joint = defaultdict(lambda: defaultdict(Q))
    for t, s in product(THETA, SHOCKS):
        joint[observation(t, s)][t] += Q(1, 64)
    ambiguous_mass = sum(sum(row.values()) for row in joint.values() if len(row) > 1)
    assert len(joint) == 48 and ambiguous_mass == Q(1, 2)
    nodes = []
    for y, row in sorted(joint.items()):
        gross, mass = [], []
        for t, w in row.items():
            for s in SHOCKS:
                gross.append(list(map(float, observation(t, s)[2:])))
                mass.append(float(w / 16))
        nodes.append((np.array(list(map(float, y[2:]))), np.array(gross), np.array(mass)))
    assert abs(sum(m.sum() for _, _, m in nodes) - 1) < 1e-14
    return nodes


def repair(x, h, target, control, buy, sell):
    """Scale the proposed trade towards zero if it overspends; never clip cash."""
    z = np.maximum(target, 0)
    if control == "E":
        z[0] = x[0]
    elif control == "N":
        z = x.copy()
    u = z - x
    spending = u.sum() + buy @ np.maximum(u, 0) + sell @ np.maximum(-u, 0)
    if spending > h:
        u *= (h / spending) * (1 - 1e-12)
    z = x + u
    cash = h - u.sum() - buy @ np.maximum(u, 0) - sell @ np.maximum(-u, 0)
    assert min(float(z.min()), float(cash)) >= -1e-14
    assert control != "E" or u[0] == 0
    assert control != "N" or np.all(u == 0)
    return z, cash


def solve(nodes, initial_cash_fraction, free_etf, root, future):
    x = np.array([0.43, (1 - initial_cash_fraction) * 0.57])
    h = initial_cash_fraction * 0.57
    buy = np.array([0.0005, 0 if free_etf else 0.0005])
    sell = np.array([0, 0 if free_etf else 0.0005])
    slopes = [np.array(s) for s in product(*[(-v, b) for v, b in zip(sell, buy)])]
    z0, c0 = cp.Variable(2, nonneg=True), cp.Variable(nonneg=True)
    constraints = [c0 + cp.sum(z0) + t @ (z0 - x) <= 1 for t in slopes]
    if root == "E":
        constraints.append(z0[0] == x[0])
    expo, targets = [], []
    for g0, g1, mass in nodes:
        incoming = cp.multiply(g0, z0)
        z1, c1 = cp.Variable(2, nonneg=True), cp.Variable(nonneg=True)
        constraints.extend(c1 + cp.sum(z1) + t @ (z1 - incoming)
                           <= c0 + cp.sum(incoming) for t in slopes)
        if future == "E":
            constraints.append(z1[0] == incoming[0])
        elif future == "N":
            constraints.append(z1 == incoming)
        expo.append(np.log(mass) - 10 * (c1 + g1 @ z1))
        targets.append(z1)
    problem = cp.Problem(cp.Minimize(cp.log_sum_exp(cp.hstack(expo))), constraints)
    problem.solve(solver="CLARABEL", tol_gap_abs=1e-9, tol_gap_rel=1e-9,
                  tol_feas=1e-9, max_iter=500)
    assert problem.status == "optimal", problem.status
    residual = max(float(np.max(c.violation())) for c in constraints)
    assert residual < 1e-7
    ce = -1000 * problem.value
    z, cash = repair(x, h, np.array(z0.value), root, buy, sell)
    replay = []
    for (g0, g1, mass), target in zip(nodes, targets):
        z1, c1 = repair(g0 * z, cash, np.array(target.value), future, buy, sell)
        replay.extend(np.log(mass) - 10 * (c1 + g1 @ z1))
    feasible_ce = -1000 * logsumexp(replay)
    assert abs(ce - feasible_ce) < 0.001  # bp; diagnostic, not an error certificate
    return ce, abs(ce - feasible_ce), residual


def main():
    # Cash clipping alone is not a funded projection, even with zero fees.
    initial_cash = Q(1)
    target = (Q(3, 5), Q(3, 5))
    clipped_cash = max(initial_cash - sum(target), Q(0))
    assert sum(target) + clipped_cash > initial_cash
    nodes = tree()
    reported = json.loads((Path(__file__).resolve().parents[2] /
                           "experiments/008/results.json").read_text())["results"]["A"]["points"]
    gaps, maximum_difference, maximum_replay, maximum_residual = {}, 0.0, 0.0, 0.0
    for schedule, c in product(("original", "ETF-free"), (0, 1)):
        ce = {}
        for d, r in product(("F", "E"), ("F", "E", "N")):
            value, replay_gap, residual = solve(nodes, c, schedule == "ETF-free", d, r)
            ce[d, r] = value
            difference = abs(value - reported[f"{schedule},{c}"]["cells"][f"{d},{r}"]["CE"])
            assert difference < 0.001
            maximum_difference = max(maximum_difference, difference)
            maximum_replay = max(maximum_replay, replay_gap)
            maximum_residual = max(maximum_residual, residual)
        gap = {r: ce["F", r] - ce["E", r] for r in ("F", "E", "N")}
        gaps[schedule, c] = (gap["E"] - gap["N"], gap["F"] - gap["E"])
        print(schedule, c, "CE contributions (bp):", gaps[schedule, c], flush=True)
    movement = np.array(gaps["original", 1]) - np.array(gaps["original", 0])
    assert movement[0] < -0.29 and movement[1] > 0.29
    assert np.max(np.abs(np.array(gaps["ETF-free", 1]) - gaps["ETF-free", 0])) < 0.001
    print("Original-cost endpoint movement (bp):", movement)
    print("Maximum CE difference from report (bp):", maximum_difference)
    print("Maximum optimizer/replayed-policy difference (bp):", maximum_replay)
    print("Maximum resource-constraint residual (dollars):", maximum_residual)
    print("Fixed witness checks passed. No rigorous optimum error bound is claimed.")


if __name__ == "__main__":
    main()
