"""Red's independent reproduction of experiment 002.

The instance stream is the registered one: run.py's part_b and part_v are executed unchanged with seed
2002, and every call to the solver under test (m1.solve) is recorded. Nothing below reuses m1.py's
formulas: the mean vector, Sigma (by scenario enumeration), admissibility, the objective, feasibility
and the optimality test are red's own code.

The optimality test is an exact KKT certificate, not an enumeration. For class F (E: coordinate 0
fixed, its condition dropped) a returned point w is certified optimal if there are multipliers
eta_B >= 0 (nonzero only if the budget is tight), eta_L_i, eta_U_i >= 0 (nonzero only at w_i = 0,
w_i = wbar_i) and subgradients zeta_i in sign(w_i - w0_i) (in [-1, 1] at w_i = w0_i) with

    g_i - eta_B - (1 + eta_B) kappa_i zeta_i + eta_L_i - eta_U_i = 0,   g = mu - gamma Sigma w.

Then w maximizes the concave Lagrangian, so for every feasible w', Qbar(w') <= L(w') <= L(w) = Qbar(w):
sufficiency needs no constraint qualification. For fixed eta_B each coordinate's condition is an
interval condition, linear in eta_B, so existence reduces to an exact intersection of intervals.

Usage: uv run python experiments/002/red_reproduce.py
"""
import itertools
import sys
from fractions import Fraction as Fr
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).parent))
import run  # noqa: E402  (registered harness and instance generator)
import m1   # noqa: E402  (solver under test)

CALLS = []
_solve = m1.solve


def recording_solve(I, cls):
    out = _solve(I, cls)
    CALLS.append((I, cls, out))
    return out


run.solve = recording_solve


# ---------------------------------------------------------------- red's own M1 objects
def red_model(I):
    """Mean vector, Sigma by exact scenario enumeration, and min gross return."""
    n = len(I.BE)
    B = [I.BA] + list(I.BE)
    mu = [I.BA[0] * I.lam[0] + I.BA[1] * I.lam[1] + I.alpha] + \
         [b[0] * I.lam[0] + b[1] * I.lam[1] - c for b, c in zip(I.BE, I.cE)]
    sizes = list(I.sf) + [I.sA] + list(I.sE)
    scen = list(itertools.product((-1, 1), repeat=len(sizes)))
    q = Fr(1, len(scen))
    d = 1 + n
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


def det(M):
    M = [row[:] for row in M]
    n, D = len(M), Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            D = -D
        D *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            for k in range(c, n):
                M[r][k] -= f * M[c][k]
    return D


def qbar(I, mu, Sig, w):
    d = len(w)
    return (sum(mu[i] * w[i] for i in range(d))
            - I.gamma / 2 * sum(w[i] * Sig[i][j] * w[j] for i in range(d) for j in range(d))
            - sum(I.kappa[i] * abs(w[i] - I.w0[i]) for i in range(d)))


def slack(I, w):
    return I.k0 - sum(w[i] - I.w0[i] for i in range(len(w))) - sum(
        I.kappa[i] * abs(w[i] - I.w0[i]) for i in range(len(w)))


def red_feasible(I, w, cls):
    ok = all(0 <= w[i] <= I.wbar[i] for i in range(len(w))) and slack(I, w) >= 0
    if cls == "E":
        ok = ok and w[0] == I.w0[0]
    if cls == "N":
        ok = ok and tuple(w) == tuple(I.w0)
    return ok


def certify(I, mu, Sig, w, cls):
    """Exact KKT certificate of global optimality (see module docstring)."""
    d = len(w)
    g = [mu[i] - I.gamma * sum(Sig[i][j] * w[j] for j in range(d)) for i in range(d)]
    lo, hi = Fr(0), None if slack(I, w) == 0 else Fr(0)      # eta_B range
    for i in range(d):
        if cls == "E" and i == 0:
            continue
        k = I.kappa[i]
        zmin, zmax = (-1, 1) if w[i] == I.w0[i] else ((1, 1) if w[i] > I.w0[i] else (-1, -1))
        at_low, at_up = w[i] == 0, w[i] == I.wbar[i]
        # need (1+eta)k zmin - [at_low]*inf <= g_i - eta <= (1+eta)k zmax + [at_up]*inf
        if not at_low:   # g_i - eta >= (1+eta) k zmin  <=>  eta <= (g_i - k zmin)/(1 + k zmin)
            ub = (g[i] - k * zmin) / (1 + k * zmin)
            hi = ub if hi is None else min(hi, ub)
        if not at_up:    # g_i - eta <= (1+eta) k zmax  <=>  eta >= (g_i - k zmax)/(1 + k zmax)
            lo = max(lo, (g[i] - k * zmax) / (1 + k * zmax))
    return hi is None or lo <= hi


# ---------------------------------------------------------------- run the registered stream
rng = np.random.default_rng(run.SEED)
brows, bfails = run.part_b()
nb = len(CALLS)
vrows, vfails = run.part_v(rng)
print("harness failures (B, V):", len(bfails), len(vfails))

fails = []
n_inst = n_sing = n_lp = n_cert = 0
seen = {}
for idx, (I, cls, (V, w, _)) in enumerate(CALLS):
    mu, Sig, mg = red_model(I)
    if mg <= 0:
        fails.append(f"call {idx}: gross return not positive")
    w = list(w)
    if not red_feasible(I, w, cls):
        fails.append(f"call {idx}: returned point infeasible ({cls})")
    if qbar(I, mu, Sig, w) != V:
        fails.append(f"call {idx}: value != red's objective at returned point ({cls})")
    if cls in ("F", "E"):
        if certify(I, mu, Sig, w, cls):
            n_cert += 1
        else:
            fails.append(f"call {idx}: no KKT certificate ({cls})")
    if idx >= nb:
        key = id(I)
        if key not in seen:
            seen[key] = {}
            n_inst += 1
            n_sing += det(Sig) == 0
            n_lp += I.gamma == 0
        seen[key].setdefault(cls, V)
nest = sum(1 for v in seen.values() if not (v["F"] >= v["E"] >= v["N"]))

# Red's own float QP (CLARABEL, tightened tolerances) for the V1 discrepancy, on the part V stream.
import cvxpy as cp  # noqa: E402
worst = 0.0
for idx, (I, cls, (V, w, _)) in enumerate(CALLS[nb:]):
    if cls == "N":
        continue
    mu, Sig, _ = red_model(I)
    d = len(mu)
    x = cp.Variable(d)
    S = np.array([[float(v) for v in r] for r in Sig])
    L = np.linalg.cholesky(S + 1e-15 * np.eye(d)) if np.all(np.linalg.eigvalsh(S) > 0) else None
    risk = cp.sum_squares(L.T @ x) if L is not None else cp.quad_form(x, cp.psd_wrap(S))
    kap = np.array([float(v) for v in I.kappa]); w0 = np.array([float(v) for v in I.w0])
    obj = np.array([float(v) for v in mu]) @ x - float(I.gamma) / 2 * risk - kap @ cp.abs(x - w0)
    cons = [x >= 0, x <= np.array([float(v) for v in I.wbar]),
            cp.sum(x - w0) + kap @ cp.abs(x - w0) <= float(I.k0)]
    if cls == "E":
        cons.append(x[0] == w0[0])
    val = cp.Problem(cp.Maximize(obj), cons).solve(solver=cp.CLARABEL, tol_gap_abs=1e-10, tol_gap_rel=1e-10, tol_feas=1e-10)
    worst = max(worst, abs(val - float(V)))

# B0 closed form, red's own: solve gamma Sigma w = mu for the recorded B0 instance (last part B call).
I0 = CALLS[nb - 1][0]
mu0, S0, _ = red_model(I0)
import sympy as sp  # noqa: E402
w_closed = list(sp.Matrix([[I0.gamma * x for x in r] for r in S0]).LUsolve(sp.Matrix(mu0)))
print("B0 lam, alpha:", I0.lam, I0.alpha, " closed form:", w_closed, " solver:", CALLS[nb - 1][2][1])

print(f"part B solver calls: {nb}; part V solver calls: {len(CALLS) - nb}")
print(f"instances {n_inst}, singular Sigma {n_sing}, gamma = 0 {n_lp}")
print(f"KKT certificates found: {n_cert} of {sum(1 for c in CALLS if c[1] != 'N')} F/E results")
print(f"nesting violations: {nest}")
print(f"max |certified value - red cvxpy|: {worst:.3e}")
print(f"failures: {len(fails)}")
for f in fails[:20]:
    print(" ", f)
sys.exit(1 if fails or bfails or vfails else 0)
