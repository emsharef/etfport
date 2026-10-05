"""Exact reference solver for small M2 instances (model/SPEC.md M2). Registered in experiments/004.

M2 = M1 with separate purchase and sale rates and ETF drag c^E of either sign. Maximizes

    Qbar(w) = mu' w - (gamma/2) w' Sigma w - tau(w - w0),
    tau(v)  = sum_i [kappa^+_i max(v_i, 0) + kappa^-_i max(-v_i, 0)],
    F = {0 <= w <= wbar,  sum_i v_i + tau(v) <= k0},  E = F with a = a0,  N = {w0},

where v = w - w0 and the rates are charged on the gross change in holdings (M2 "Directional
proportional switching costs and charged amounts"). Qbar depends on the belief only through its mean.

Method: the sign-piece enumeration of experiments/002/m1.py, with the rate chosen by the piece's sign.
On the piece P_s = {w in F : s_i (w_i - w0_i) >= 0} one has tau(v) = sum_i rho_i s_i v_i with
rho_i = kappa^+_i if s_i = +1 and kappa^-_i if s_i = -1 (both formulas give 0 where v_i = 0), so the
objective is the concave quadratic f_s(w) = (mu - rho*s)' w - (gamma/2) w' Sigma w + sum rho_i s_i w0_i
and the budget is the linear constraint sum_i (1 + rho_i s_i)(w_i - w0_i) <= k0, with 1 + rho_i s_i > 0
because every rate is below one. P_s is a nonempty compact polytope containing w0. The extreme-point
argument in m1.py's docstring applies unchanged: an extreme point of the optimal set of f_s on P_s is the
unique stationary point of f_s on the affine hull of its minimal face, and that hull fixes some
coordinates at 0, wbar_i or w0_i and possibly makes the budget tight. Enumerating all such affine sets,
keeping the feasible stationary points and taking the best by the true objective gives the exact maximum.
Signed c^E only changes mu. Exact over Fraction; float mode is for screening only.
"""
from __future__ import annotations

import sys
from dataclasses import dataclass
from fractions import Fraction as Fr
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "002"))
from m1 import _solve_linear, mean_vector, positive_definite, scenarios, sigma_formula, sigma_from_scenarios  # noqa: E402,F401


@dataclass(frozen=True)
class Instance2:
    BA: tuple
    BE: tuple
    sf: tuple
    sA: object
    sE: tuple
    lam: tuple
    alpha: object
    cE: tuple            # ETF drag, either sign (M2)
    gamma: object
    kbuy: tuple          # purchase rates kappa^+ (1+n,), charged on value delivered
    ksell: tuple         # sale rates kappa^- (1+n,), charged on gross value removed
    w0: tuple
    k0: object
    wbar: tuple

    @property
    def n(self) -> int:
        return len(self.BE)

    @property
    def d(self) -> int:
        return 1 + len(self.BE)


def check_instance(I: Instance2) -> list[str]:
    errs = []
    if sigma_from_scenarios(I) != sigma_formula(I):
        errs.append("scenario covariance differs from B Sf B' + D")
    mu = mean_vector(I)
    for _, _, xi in scenarios(I):
        if any(1 + mu[i] + xi[i] <= 0 for i in range(I.d)):
            errs.append("gross return not strictly positive in some scenario")
            break
    if any(x < 0 for x in I.w0) or I.k0 < 0 or sum(I.w0) + I.k0 != 1:
        errs.append("pre-trade positions are not a funded long-only allocation")
    if any(not (0 <= k < 1) for k in I.kbuy + I.ksell):
        errs.append("a rate outside [0, 1)")
    if any(not (0 <= w <= b <= 1) for w, b in zip(I.w0, I.wbar)):
        errs.append("position limits violated or outside [0, 1]")
    if I.gamma < 0:
        errs.append("negative risk coefficient")
    return errs


def tau(I: Instance2, v) -> object:
    return sum(I.kbuy[i] * v[i] if v[i] > 0 else -I.ksell[i] * v[i] for i in range(I.d))


def objective(I: Instance2, S, mu, w):
    d = I.d
    v = [w[i] - I.w0[i] for i in range(d)]
    quad = sum(w[i] * S[i][j] * w[j] for i in range(d) for j in range(d))
    return sum(mu[i] * w[i] for i in range(d)) - I.gamma / 2 * quad - tau(I, v)


def feasible(I: Instance2, w, tol=0) -> bool:
    d = I.d
    if any(w[i] < -tol or w[i] > I.wbar[i] + tol for i in range(d)):
        return False
    v = [w[i] - I.w0[i] for i in range(d)]
    return sum(v) + tau(I, v) <= I.k0 + tol


def solve(I: Instance2, cls: str = "F", exact: bool = True):
    """Return (value, optimal point, list of distinct optimal candidates) for class F, E or N."""
    conv = (lambda x: Fr(x)) if exact else float
    d = I.d
    S = [[conv(x) for x in row] for row in sigma_formula(I)]
    mu = [conv(x) for x in mean_vector(I)]
    g = conv(I.gamma)
    kb, ks = [conv(x) for x in I.kbuy], [conv(x) for x in I.ksell]
    w0, wbar, k0 = [conv(x) for x in I.w0], [conv(x) for x in I.wbar], conv(I.k0)
    Ic = Instance2(I.BA, I.BE, I.sf, I.sA, I.sE, I.lam, I.alpha, I.cE, g, tuple(kb), tuple(ks), tuple(w0), k0,
                   tuple(wbar))
    tol = 0 if exact else 1e-12
    if cls == "N":
        return objective(Ic, S, mu, w0), list(w0), [list(w0)]
    H = [[g * S[i][j] for j in range(d)] for i in range(d)]
    opts = []
    for i in range(d):
        if cls == "E" and i == 0:
            opts.append([w0[0]])
        else:
            vals = []
            for x in (None, conv(0), wbar[i], w0[i]):
                if x is None or all(x != y for y in vals if y is not None):
                    vals.append(x)
            opts.append(vals)
    best, best_w, optima, seen = None, None, [], set()
    for s in product((1, -1), repeat=d):
        rho = [kb[i] if s[i] == 1 else ks[i] for i in range(d)]
        lin = [mu[i] - rho[i] * s[i] for i in range(d)]
        c = [1 + rho[i] * s[i] for i in range(d)]
        for fix in product(*opts):
            F = [i for i in range(d) if fix[i] is None]
            for beq in ((False, True) if F else (False,)):
                m = len(F)
                rhs = [lin[i] - sum(H[i][j] * fix[j] for j in range(d) if fix[j] is not None) for i in F]
                if beq:
                    A = [[H[F[a]][F[b]] for b in range(m)] + [c[F[a]]] for a in range(m)]
                    A.append([c[F[b]] for b in range(m)] + [conv(0)])
                    brhs = k0 + sum(c[i] * w0[i] for i in range(d)) - \
                        sum(c[j] * fix[j] for j in range(d) if fix[j] is not None)
                    sol = _solve_linear(A, rhs + [brhs], exact)
                else:
                    A = [[H[F[a]][F[b]] for b in range(m)] for a in range(m)]
                    sol = _solve_linear(A, rhs, exact) if m else []
                if sol is None:
                    continue
                w = [fix[i] for i in range(d)]
                for a, i in enumerate(F):
                    w[i] = sol[a]
                if any(s[i] * (w[i] - w0[i]) < -tol for i in range(d)) or not feasible(Ic, w, tol):
                    continue
                key = tuple(w) if exact else tuple(round(x, 12) for x in w)
                if key in seen:
                    continue
                seen.add(key)
                val = objective(Ic, S, mu, w)
                if best is None or val > best + (0 if exact else 1e-15):
                    best, best_w, optima = val, w, [w]
                elif (exact and val == best) or (not exact and abs(val - best) <= 1e-15):
                    optima.append(w)
    return best, best_w, optima
