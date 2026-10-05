"""Red's review of the M3 definition (model/SPEC.md, M3): an independent attack, not a claim.

Run: uv run python checks/red-m3-definition/check.py

Part A (exact rationals): Bayes bookkeeping, the dollar cash equation, post-trade wealth
positivity, the marked review-1 state as a function of (u_0, y) only, and the first-review
substitution identity sum_i w_i + k(w) + tau(v) = 1 of the "First-review transfer" section.

Part B (floating point, CLARABEL): the whole M3 root problem is one finite convex program in
(u_0, {u_1(y)}): terminal wealth is affine minus convex costs, U_rho is increasing and concave,
and the funding sets are convex. Two assumed instances are solved with the review-0 class in
{F, E, N} and the review-1 class in {F, E, N}. M3 names only continuation F_1 and the matched
control N_1 (u_1 = 0). The E_1 arm shows that the F_1-versus-N_1 contrast adds two channels that
can have opposite signs: future ETF-only adjustment and future active trading. Every value
is rechecked by fixing u_0 and solving each observation's review-1 problem separately (the
finite dynamic-programming decomposition); floating numerics, not exact certificates.

Part C (after M3's continuation-control correction): an interim SPEC measured G_R = V_{F,R} - V_{E,R}
in expected-utility units. Instance C shows that the sign of the future-ETF channel G_E - G_N
depends on that choice: positive in certainty-equivalent terms, negative in utility units. The
final SPEC uses Delta_R = CE_{F,R} - CE_{E,R}; Part C also re-solves instance C with a sure terminal
payoff added under E_1 only, confirming that Delta_E is unchanged while G_E - G_N moves.
"""
from collections import defaultdict
from fractions import Fraction as Fr
from itertools import product
import random
import sys

import cvxpy as cp
import numpy as np


def make(BA, BE, cE, lam1, lam2, alphas, sizes, kb, ks, x0, rho):
    n = len(BE)
    Theta = [(l, lam2, a) for l in lam1 for a in alphas]
    shocks = []
    for sg in product((-1, 1), repeat=3 + n):
        z = [s * c for s, c in zip(sg, sizes)]
        shocks.append((Fr(1, 2 ** (3 + n)), (z[0], z[1]), z[2], tuple(z[3:])))
    return dict(BA=BA, BE=BE, cE=cE, Theta=Theta, pi0={t: Fr(1, len(Theta)) for t in Theta},
                shocks=shocks, kb=kb, ks=ks, x0=x0, h0=1 - sum(x0), rho=rho)


F = Fr
# Instance A: one ETF with loading (1, 0); uncertain lambda_1 and alpha; tiny rates. Review 1
# identifies lambda_1 but alpha only for some observations (partial learning).
INST_A = make(BA=(F(23, 25), F(31, 50)), BE=((F(1), F(0)),), cE=(F(3, 10000),),
              lam1=(F(1, 100), F(1, 25)), lam2=F(1, 100), alphas=(F(-1, 100), F(1, 50)),
              sizes=(F(9, 100), F(2, 25), F(3, 200), F(1, 100)),
              kb=(F(1, 2000), F(1, 2000)), ks=(F(0), F(1, 2000)),
              x0=(F(43, 100), F(1767, 10000)), rho=F(10))
# Instance B: two ETFs with full-rank loadings. Its shocks are large relative to the gaps in
# Theta, so review 1 reveals theta exactly (permitted by M3, not imposed).
INST_B = make(BA=(F(93, 100), F(99, 100)), BE=((F(1), F(0)), (F(3, 100), F(19, 25))),
              cE=(F(-1, 10000), F(1, 5000)),
              lam1=(F(1, 50), F(1, 25)), lam2=F(1, 100), alphas=(F(-1, 100), F(0)),
              sizes=(F(1, 20), F(1, 100), F(7, 100), F(1, 20), F(3, 50)),
              kb=(F(1, 100), F(1, 400), F(1, 2000)), ks=(F(1, 400), F(0), F(1, 100)),
              x0=(F(49, 100), F(51, 10000), F(51, 10000)), rho=F(5))
# Instance C: one ETF; the channel decomposition's sign depends on the scale (Part C).
INST_C = make(BA=(F(28, 25), F(19, 25)), BE=((F(1), F(0)),), cE=(F(0),),
              lam1=(F(0), F(3, 100)), lam2=F(1, 100), alphas=(F(-1, 100), F(1, 100)),
              sizes=(F(3, 100), F(3, 50), F(7, 100), F(1, 50)),
              kb=(F(1, 2000), F(0)), ks=(F(1, 2000), F(1, 400)),
              x0=(F(51, 100), F(833, 10000)), rho=F(20))


def returns(I, theta, s):
    lam1, lam2, alpha = theta
    _, zf, zA, zE = s
    f = (lam1 + zf[0], lam2 + zf[1])
    rA = I["BA"][0] * f[0] + I["BA"][1] * f[1] + alpha + zA
    rE = tuple(b[0] * f[0] + b[1] * f[1] - c + z for b, c, z in zip(I["BE"], I["cE"], zE))
    return f, (rA,) + rE


def bayes(I):
    L = {t: defaultdict(Fr) for t in I["Theta"]}
    for t in I["Theta"]:
        for s in I["shocks"]:
            L[t][returns(I, t, s)] += s[0]
    Y = sorted(set().union(*[set(v) for v in L.values()]))
    P0 = {y: sum(I["pi0"][t] * L[t][y] for t in I["Theta"]) for y in Y}
    post = {y: {t: I["pi0"][t] * L[t][y] / P0[y] for t in I["Theta"]} for y in Y}
    return Y, P0, post


def dollar_cost(u, kb, ks):
    return sum(p * max(x, 0) + m * max(-x, 0) for x, p, m in zip(u, kb, ks))


def part_a(I, rng):
    fails = []
    Y, P0, post = bayes(I)
    if sum(P0.values()) != 1:
        fails.append("P0 does not sum to one")
    for t in I["Theta"]:
        if sum(P0[y] * post[y][t] for y in Y) != I["pi0"][t]:
            fails.append("posterior does not average to the prior")
    for y in Y:
        if sum(post[y].values()) != 1:
            fails.append("posterior does not sum to one")
    ambiguous = sum(1 for y in Y if sum(1 for t in I["Theta"] if post[y][t] > 0) > 1)
    moved = sum(1 for y in Y if any(post[y][t] != I["pi0"][t] for t in I["Theta"]))
    for t, s in product(I["Theta"], I["shocks"]):
        if any(1 + r <= 0 for r in returns(I, t, s)[1]):
            fails.append("nonpositive gross return")
    kb, ks, x0, h0 = I["kb"], I["ks"], I["x0"], I["h0"]
    d, trades = len(x0), 0
    for _ in range(300):
        u = [Fr(rng.randint(-1000, 1000), 1000) * (x0[i] + h0) for i in range(d)]
        u = [max(ui, -x0[i]) for i, ui in enumerate(u)]
        h = h0 - sum(u) - dollar_cost(u, kb, ks)
        if h < 0:
            continue
        trades += 1
        x = [a + b for a, b in zip(x0, u)]
        W0, C = sum(x0) + h0, dollar_cost(u, kb, ks)
        if sum(x) + h != W0 - C:
            fails.append("cash equation: post-trade wealth != W^- - C(u)")
        if not sum(x) + h > 0:
            fails.append("post-trade wealth not positive")
        w, k, v = [xi / W0 for xi in x], h / W0, [ui / W0 for ui in u]
        tau = dollar_cost(v, kb, ks)
        if sum(w) + k + tau != 1 or any(wi > 1 for wi in w):
            fails.append("first-review identity sum w + k + tau = 1 (hence w_i <= 1) fails")
        # The marked review-1 state is a function of (u_0, y) alone, so it reveals nothing beyond y.
        seen = {}
        for t, s in product(I["Theta"], I["shocks"]):
            y = returns(I, t, s)
            state = (tuple(xi * (1 + r) for xi, r in zip(x, y[1])), h)
            if seen.setdefault(y, state) != state:
                fails.append("marked state differs across hidden histories with the same y")
    return dict(obs=len(Y), ambiguous=ambiguous, moved=moved, trades=trades), fails


def _cost(u, kb, ks):
    return kb @ cp.pos(u) + ks @ cp.neg(u)


def solve(I, B, root, cont, fix_uA=None, state0=None, shift=0.0):
    """Value (expected U_rho(W_2/W_0), W_0 = 1) of the M3 problem with the review-0 class `root`
    and review-1 class `cont` for every observation, as one convex program. With state0 = (x, h)
    the post-review-0 state is a given constant instead (the per-observation recheck)."""
    Y, P0, post = B
    d = len(I["x0"])
    kb = np.array([float(x) for x in I["kb"]]); ks = np.array([float(x) for x in I["ks"]])
    x0 = np.array([float(x) for x in I["x0"]]); h0 = float(I["h0"]); rho = float(I["rho"])
    if state0 is None:
        u0 = cp.Variable(d)
        cons = [x0 + u0 >= 0, h0 - cp.sum(u0) - _cost(u0, kb, ks) >= 0]
        cons += {"F": [], "E": [u0[0] == 0], "N": [u0 == 0]}[root]
        if fix_uA is not None:
            cons.append(u0[0] == fix_uA)
        x0p, h0p = x0 + u0, h0 - cp.sum(u0) - _cost(u0, kb, ks)
    else:
        u0, cons = None, []
        x0p, h0p = state0
    expo, mass = [], []
    for y in Y:
        if P0[y] == 0:
            continue
        x1 = cp.multiply(np.array([1 + float(r) for r in y[1]]), x0p)
        u1 = cp.Variable(d)
        cons += [x1 + u1 >= 0, h0p - cp.sum(u1) - _cost(u1, kb, ks) >= 0]
        cons += {"F": [], "E": [u1[0] == 0], "N": [u1 == 0]}[cont]
        h1p = h0p - cp.sum(u1) - _cost(u1, kb, ks)
        rows = []
        for t, pt in post[y].items():
            if pt > 0:
                for s in I["shocks"]:
                    rows.append([1 + float(r) for r in returns(I, t, s)[1]])
                    mass.append(float(P0[y] * pt * s[0]))
        # Utility is rescaled by exp(rho) for conditioning; undone below.
        expo.append(-rho * (h1p + np.array(rows) @ (x1 + u1) + shift - 1))
    prob = cp.Problem(cp.Minimize(cp.sum(cp.multiply(np.array(mass), cp.exp(cp.hstack(expo))))), cons)
    prob.solve(solver="CLARABEL")
    if prob.status != "optimal":
        raise RuntimeError(f"solver status {prob.status}")
    return -prob.value * np.exp(-rho), (None if u0 is None else u0.value)


def bp(v, rho):
    """Certainty equivalent of terminal wealth / W_0, in basis points."""
    return -np.log(-v) / float(rho) * 1e4


def funded_projection(x, h, u, kb, ks):
    """Map a proposed trade u at state (x, h) into the funded set without creating wealth:
    cap each sale at the holding, then scale the whole trade toward zero until cash is
    nonnegative. Scaling keeps any coordinate fixed at zero (the E and N restrictions), and
    since x >= 0 and every sale is capped, x + t u >= 0 for every t in [0, 1]."""
    u = np.maximum(u, -x)
    need = u.sum() + kb @ np.maximum(u, 0) + ks @ np.maximum(-u, 0)
    if need > h:
        u = u * (h / need)        # need > h >= 0; the fee is positively homogeneous
    cash = h - u.sum() - kb @ np.maximum(u, 0) - ks @ np.maximum(-u, 0)
    return x + u, cash, u      # cash may be -1e-17 from rounding; never rounded up


def nested(I, B, cont, u0):
    """Per-observation recheck: fix u_0 after a funded projection, then solve each observation's
    review-1 problem on its own. It measures agreement between two numerical procedures; it is
    not a certified bound on the optimum error (see experiments/008/red_reproduce.py for a
    bracket). An earlier version clipped negative cash to zero without changing holdings, which
    could add wealth; it was replaced on 2026-09-28 after math's note."""
    Y, P0, post = B
    kb = np.array([float(x) for x in I["kb"]]); ks = np.array([float(x) for x in I["ks"]])
    x0 = np.array([float(x) for x in I["x0"]])
    x, h, _ = funded_projection(x0, float(I["h0"]), np.asarray(u0, dtype=float), kb, ks)
    assert h > -1e-12 and (x >= 0).all()
    rho, total = float(I["rho"]), 0.0
    for y in Y:
        if P0[y] == 0:
            continue
        if cont == "N":  # no review-1 decision: evaluate the fixed policy directly
            x1 = x * np.array([1 + float(r) for r in y[1]])
            total += sum(float(P0[y] * pt * s[0]) * -np.exp(-rho * (h + x1 @ np.array(
                [1 + float(r) for r in returns(I, t, s)[1]]))) for t, pt in post[y].items() if pt > 0
                for s in I["shocks"])
        else:
            total += float(P0[y]) * solve(I, ([y], {y: Fr(1)}, {y: post[y]}), None, cont, state0=(x, h))[0]
    return total


def part_b(name, I):
    B = bayes(I)
    rho = I["rho"]
    V, U, recheck = {}, {}, 0.0
    for root, cont in product("FEN", "FEN"):
        V[root, cont], U[root, cont] = solve(I, B, root, cont)
        recheck = max(recheck, abs(bp(V[root, cont], rho) - bp(nested(I, B, cont, U[root, cont]), rho)))
    print(f"\n### Instance {name}: certainty equivalents (bp of W_0) and root active trade\n")
    print("| review-1 class | CE root F | CE root E | CE root N | gap F-E (bp) | root F active trade u_0,A |")
    print("|---|---|---|---|---|---|")
    G = {}
    for c in "FEN":
        G[c] = bp(V["F", c], rho) - bp(V["E", c], rho)
        print(f"| {c}_1 | {bp(V['F', c], rho):.4f} | {bp(V['E', c], rho):.4f} | {bp(V['N', c], rho):.4f} "
              f"| {G[c]:.4f} | {U['F', c][0]:+.6f} |")
    print(f"\nM3's matched contrast G(F_1) - G(N_1) = {G['F'] - G['N']:+.4f} bp"
          f" = future active channel G(F_1) - G(E_1) = {G['F'] - G['E']:+.4f}"
          f" + future ETF channel G(E_1) - G(N_1) = {G['E'] - G['N']:+.4f}.")
    print(f"Max |joint - nested H_0 recheck| over the 9 cells: {recheck:.2e} bp.")
    return B, G, U, recheck


def phi(I, B, cont, a):
    """Best value with root class F and the root active trade fixed at a (concave in a)."""
    return bp(solve(I, B, "F", cont, fix_uA=a)[0], I["rho"])


def part_c(I):
    """An interim M3 SPEC took G_R = V_{F,R} - V_{E,R} in expected-utility units. Under CARA the
    translation-invariant scale is the certainty equivalent, CE = -ln(-V)/rho, whose gap is
    -(1/rho) ln(V_F/V_E). Each G_R has the same sign on both scales; the channels need not."""
    B, rho = bayes(I), I["rho"]
    sol = {(D, R): solve(I, B, D, R) for D in "FE" for R in "FEN"}
    V = {k: v for k, (v, _) in sol.items()}
    rel = max(abs(nested(I, B, R, u0) / V[D, R] - 1) for (D, R), (_, u0) in sol.items())
    GU = {R: V["F", R] - V["E", R] for R in "FEN"}
    GC = {R: bp(V["F", R], rho) - bp(V["E", R], rho) for R in "FEN"}
    print("\n### Instance C: the continuation channels on the utility and certainty-equivalent scales\n")
    print("| Quantity | utility units | certainty equivalent (bp of W_0) |\n|---|---|---|")
    for R in "FEN":
        print(f"| G_{R} | {GU[R]:.4e} | {GC[R]:.4f} |")
    print(f"| G_E - G_N (future ETF adjustment) | {GU['E'] - GU['N']:+.4e} | {GC['E'] - GC['N']:+.4f} |")
    print(f"| G_F - G_E (future active trading) | {GU['F'] - GU['E']:+.4e} | {GC['F'] - GC['E']:+.4f} |")
    print(f"\nRelative size of the utility-scale ETF channel: {(GU['E'] - GU['N']) / GU['N']:+.3%} of G_N; "
          f"max relative |joint - nested recheck| of the six values: {rel:.1e}.")
    delta = 0.01   # sure terminal payoff of 1% of W_0 under E_1 only, for both root classes
    VS = {D: solve(I, B, D, "E", shift=delta)[0] for D in "FE"}
    dce = bp(VS["F"], rho) - bp(VS["E"], rho)
    gu = VS["F"] - VS["E"]
    print(f"With a sure terminal payoff of {delta:.0%} of W_0 under E_1 only: Delta_E {GC['E']:.4f} -> {dce:.4f} bp; "
          f"utility channel G_E - G_N {GU['E'] - GU['N']:+.4e} -> {gu - GU['N']:+.4e}.")
    return GU, GC, rel, dce - GC["E"], (gu - GU["N"]) - (GU["E"] - GU["N"])


def main():
    rng = random.Random(3003)
    fails = []
    print("### Part A: exact accounting (rationals)\n\n| Instance | observations | ambiguous y | "
          "posterior moved | random funded trades checked |\n|---|---|---|---|---|")
    for name, I in (("A", INST_A), ("B", INST_B)):
        row, f = part_a(I, rng)
        fails += f
        print(f"| {name} | {row['obs']} | {row['ambiguous']} | {row['moved']} | {row['trades']} |")

    _, GA, UA, rA = part_b("A", INST_A)
    if not (GA["F"] - GA["E"] < -1 and GA["E"] - GA["N"] > 1):
        fails.append("A: the two continuation channels do not have opposite signs of at least 1 bp")
    if not abs(UA["F", "E"][0] - UA["F", "F"][0]) > 10 * abs(UA["F", "F"][0] - UA["F", "N"][0]):
        fails.append("A: root active trade pattern not as reported")

    B, GB, UB, rB = part_b("B", INST_B)
    eps = 0.001
    print("\nInstance B, best CE (bp) with root class F and the root active trade fixed at a. The partial "
          "maximum phi(a) is concave, so phi(0) > phi(-eps), phi(eps) puts the maximizer in (-eps, eps), and "
          "phi(-eps) > phi(0) puts it below zero.\n")
    print("| review-1 class | a = -0.001 | a = 0 | a = +0.001 | maximizer in (-0.001, 0.001)? |\n|---|---|---|---|---|")
    stay = {}
    for c in "FEN":
        m, z, p = phi(INST_B, B, c, -eps), phi(INST_B, B, c, 0.0), phi(INST_B, B, c, eps)
        stay[c] = z > m and z > p
        if c == "E" and not m > z:
            fails.append("B: E_1 maximizer not shown to be negative")
        print(f"| {c}_1 | {m:.6f} | {z:.6f} | {p:.6f} | {'yes' if stay[c] else 'no'} |")
    if not (stay["F"] and stay["N"] and not stay["E"]):
        fails.append("B: expected root active trade near zero under F_1 and N_1, negative under E_1")
    GU, GC, rC, dshift, ushift = part_c(INST_C)
    if abs(dshift) > 1e-4 or abs(ushift) < 1e-3 * abs(GU["N"]):
        fails.append("C: expected Delta_E invariant and G_E - G_N moved by a sure terminal shift under E_1")
    if rC > 1e-6:
        fails.append(f"C: nested recheck differs by relative {rC:.1e}")
    if not (GC["E"] - GC["N"] > 1 and (GU["E"] - GU["N"]) < -1e-3 * abs(GU["N"])):
        fails.append("C: expected the ETF channel positive in CE (> 1 bp) and negative in utility units")
    if any((GU[R] > 0) != (GC[R] > 0) for R in "FEN"):
        fails.append("C: a gap G_R changed sign between scales (impossible for a monotone transform)")
    if max(rA, rB) > 1e-4:
        fails.append(f"nested recheck disagrees by {max(rA, rB):.2e} bp")
    print(f"\nFailures: {len(fails)}")
    for f in fails:
        print("-", f)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
