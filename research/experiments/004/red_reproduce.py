"""Red's independent reproduction of experiment 004.

The registered instance stream is used unchanged: run.py's part_b and part_v with seed 2004, recording
every call to the solver under test (m2.solve, including V4's embedded M1 instances). Everything that
judges the solver is red's own code: mean vector with signed drag, Sigma by scenario enumeration,
gross-return positivity, objective with directional costs, feasibility, and an exact KKT certificate.

Certificate (class F; for E coordinate 0 is fixed and its condition dropped). With g = mu - gamma Sigma w
and v = w - w0, w is globally optimal if there exist eta_B >= 0 (nonzero only if the budget is tight),
eta_L_i, eta_U_i >= 0 (nonzero only at w_i = 0, w_i = wbar_i) and zeta_i in the subdifferential of
kappa^+_i max(v_i, 0) + kappa^-_i max(-v_i, 0), i.e. {kappa^+_i} if v_i > 0, {-kappa^-_i} if v_i < 0 and
[-kappa^-_i, kappa^+_i] if v_i = 0, with

    g_i - eta_B - (1 + eta_B) zeta_i + eta_L_i - eta_U_i = 0.

Then w maximizes the concave Lagrangian, so Qbar(w') <= L(w') <= L(w) = Qbar(w) for every feasible w'
(sufficiency needs no constraint qualification). For fixed eta_B each coordinate gives an interval
condition linear in eta_B, so existence is an exact interval intersection.

Usage: uv run python experiments/004/red_reproduce.py
"""
import itertools
import sys
from fractions import Fraction as Fr
from pathlib import Path

import numpy as np
import sympy as sp

sys.path.insert(0, str(Path(__file__).parent))
import run  # noqa: E402  (registered harness)
import m2   # noqa: E402  (solver under test)

CALLS = []
_solve = m2.solve


def recording_solve(I, cls):
    out = _solve(I, cls)
    CALLS.append((I, cls, out))
    return out


run.solve = recording_solve


def red_model(I):
    n = len(I.BE)
    B = [I.BA] + list(I.BE)
    mu = [I.BA[0] * I.lam[0] + I.BA[1] * I.lam[1] + I.alpha] + \
         [b[0] * I.lam[0] + b[1] * I.lam[1] - c for b, c in zip(I.BE, I.cE)]
    sizes = list(I.sf) + [I.sA] + list(I.sE)
    scen = list(itertools.product((-1, 1), repeat=len(sizes)))
    q, d = Fr(1, len(scen)), 1 + n
    Sig = [[Fr(0)] * d for _ in range(d)]
    min_gross = None
    for sg in scen:
        z = [s * x for s, x in zip(sg, sizes)]
        xi = [B[i][0] * z[0] + B[i][1] * z[1] + z[2 + i] for i in range(d)]
        for i in range(d):
            for j in range(d):
                Sig[i][j] += q * xi[i] * xi[j]
            g = 1 + mu[i] + xi[i]
            min_gross = g if min_gross is None else min(min_gross, g)
    return mu, Sig, min_gross


def cost(I, w):
    return sum(I.kbuy[i] * max(w[i] - I.w0[i], 0) + I.ksell[i] * max(I.w0[i] - w[i], 0)
               for i in range(len(w)))


def qbar(I, mu, Sig, w):
    d = len(w)
    return (sum(mu[i] * w[i] for i in range(d))
            - I.gamma / 2 * sum(w[i] * Sig[i][j] * w[j] for i in range(d) for j in range(d)) - cost(I, w))


def slack(I, w):
    return I.k0 - sum(w[i] - I.w0[i] for i in range(len(w))) - cost(I, w)


def red_feasible(I, w, cls):
    ok = all(0 <= w[i] <= I.wbar[i] for i in range(len(w))) and slack(I, w) >= 0
    if cls == "E":
        ok = ok and w[0] == I.w0[0]
    if cls == "N":
        ok = ok and tuple(w) == tuple(I.w0)
    return ok


def certify(I, mu, Sig, w, cls):
    d = len(w)
    g = [mu[i] - I.gamma * sum(Sig[i][j] * w[j] for j in range(d)) for i in range(d)]
    lo, hi = Fr(0), None if slack(I, w) == 0 else Fr(0)
    for i in range(d):
        if cls == "E" and i == 0:
            continue
        if w[i] > I.w0[i]:
            zmin = zmax = I.kbuy[i]
        elif w[i] < I.w0[i]:
            zmin = zmax = -I.ksell[i]
        else:
            zmin, zmax = -I.ksell[i], I.kbuy[i]
        if w[i] != 0:              # g_i - eta >= (1 + eta) zmin
            ub = (g[i] - zmin) / (1 + zmin)
            hi = ub if hi is None else min(hi, ub)
        if w[i] != I.wbar[i]:      # g_i - eta <= (1 + eta) zmax
            lo = max(lo, (g[i] - zmax) / (1 + zmax))
    return hi is None or lo <= hi


rng = np.random.default_rng(run.SEED)
brows, bfails = run.part_b()
nb = len(CALLS)
vrows, vfails = run.part_v(rng)
print("harness failures (B, V):", len(bfails), len(vfails))

fails, seen = [], {}
n_cert = n_fe = 0
for idx, (I, cls, (V, w, _)) in enumerate(CALLS):
    mu, Sig, mg = red_model(I)
    w = list(w)
    if mg <= 0:
        fails.append(f"call {idx}: a gross return is not positive")
    if not red_feasible(I, w, cls):
        fails.append(f"call {idx}: returned point infeasible ({cls})")
    if qbar(I, mu, Sig, w) != V:
        fails.append(f"call {idx}: value != red's objective ({cls})")
    if cls in ("F", "E"):
        n_fe += 1
        if certify(I, mu, Sig, w, cls):
            n_cert += 1
        else:
            fails.append(f"call {idx}: no KKT certificate ({cls})")
    if idx >= nb:
        # keyed by value: V4 rebuilds its embedded instance once per class
        seen.setdefault(I, (I, Sig, {}))[2].setdefault(cls, V)

m2_inst = [(I, S, v) for I, S, v in seen.values() if "N" in v]          # part V M2 instances
emb = [(I, S, v) for I, S, v in seen.values() if "N" not in v]           # V4 embedded M1 instances
det = lambda M: sp.Matrix(M).det()
print(f"part V M2 instances {len(m2_inst)}: asymmetric {sum(I.kbuy != I.ksell for I, _, _ in m2_inst)}, "
      f"negative drag {sum(any(c < 0 for c in I.cE) for I, _, _ in m2_inst)}, "
      f"singular Sigma {sum(det(S) == 0 for _, S, _ in m2_inst)}, gamma = 0 {sum(I.gamma == 0 for I, _, _ in m2_inst)}")
print(f"nesting violations: {sum(not (v['F'] >= v['E'] >= v['N']) for _, _, v in m2_inst)}")
print(f"V4 embedded instances: {len(emb)} (symmetric: {all(I.kbuy == I.ksell for I, _, _ in emb)})")
print(f"KKT certificates: {n_cert} of {n_fe} F/E results")

# B1, red's own derivation: binding budget p = 1 - (1 + k) a; maximize the resulting quadratic in a.
I_b1 = CALLS[0][0]
mu, Sig, _ = red_model(I_b1)
a = sp.Symbol("a")
k = I_b1.kbuy[0]
p = 1 - (1 + k) * a
f = mu[0] * a + mu[1] * p - I_b1.gamma / 2 * (Sig[0][0] * a**2 + 2 * Sig[0][1] * a * p + Sig[1][1] * p**2) - k * a
a_star = sp.solve(sp.diff(f, a), a)[0]
p_star = p.subs(a, a_star)
mult = mu[1] - I_b1.gamma * (Sig[1][0] * a_star + Sig[1][1] * p_star)       # d f / d p at the point
print("B1 red:", a_star, p_star, "precondition", 0 < a_star < 1 and 0 < p_star < 1 and mult >= 0,
      "| solver:", CALLS[0][2][1], "| KKT-certified:", certify(I_b1, mu, Sig, [Fr(str(a_star)), Fr(str(p_star))], "F"))
# B2
L = Fr(575, 10000)
kp = L / (1 - L)
x = Fr(1, 10)
print("B2:", kp, round(float(kp) * 10000), x + kp * x, x / (1 - L))

print(f"failures: {len(fails)}")
for f_ in fails[:20]:
    print(" ", f_)
sys.exit(1 if fails or bfails or vfails else 0)
