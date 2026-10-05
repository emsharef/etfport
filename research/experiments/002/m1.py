"""Exact reference solver for small M1 instances (model/SPEC.md M1). Registered in experiments/002.

Maximizes the M1 belief-average score over the full class F, the ETF-only class E or no trade N:

    Qbar(w) = mu' w - (gamma/2) w' Sigma w - sum_i kappa_i |w_i - w0_i|
    F = {0 <= w <= wbar,  sum_i (w_i - w0_i) + sum_i kappa_i |w_i - w0_i| <= k0},  E = F with a = a0.

Qbar depends on the belief only through its mean, so an instance carries the mean (lam, alpha).

Method (exact over Fraction; the same code runs over float for screening, never for certification).
The feasible set is covered by the 2^d sign pieces P_s = {w in F: s_i (w_i - w0_i) >= 0}. On P_s the
objective is the concave quadratic f_s(w) = (mu - kappa*s)' w - (gamma/2) w' Sigma w + sum kappa_i s_i w0_i
and every constraint is linear. P_s is a nonempty (it contains w0) compact polytope, so the optimal set
of f_s on P_s is a nonempty compact convex set and has an extreme point x. Let G be the minimal face of
P_s containing x; its affine hull is cut out by the constraints active at x, each of which fixes a
coordinate (to 0, wbar_i or w0_i) or makes the budget tight. x lies in the relative interior of G, so the
gradient of f_s at x is orthogonal to aff(G). If the Hessian restricted to the directions of aff(G) had a
null direction d, f_s would be constant on x + t d and x +- t d would be optimal points of G for small t,
contradicting extremality. So x is the unique stationary point of f_s on aff(G). The solver enumerates
every such affine set (each coordinate free or fixed to one of its three values; budget tight or not),
solves the stationarity system when it is nonsingular, keeps the candidates feasible for P_s and returns
the best by the true objective. Every candidate is feasible, and x is among them, so the returned value
is the exact maximum of Qbar over the class and the returned point is an optimal point.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr
from itertools import product


@dataclass(frozen=True)
class Instance:
    BA: tuple            # active loadings (2,)
    BE: tuple            # ETF loadings, n rows of (2,)
    sf: tuple            # factor shock sizes: each factor shock is +-sf_k with probability 1/2
    sA: object           # active residual shock size
    sE: tuple            # ETF residual shock sizes (n,)
    lam: tuple           # belief-mean factor premia (2,)
    alpha: object        # belief-mean alpha
    cE: tuple            # ETF drag (n,)
    gamma: object
    kappa: tuple         # proportional switching cost rates (1+n,)
    w0: tuple            # pre-trade positions normalized by pre-trade wealth (1+n,)
    k0: object           # pre-trade cash share
    wbar: tuple          # position limits (1+n,)

    @property
    def n(self) -> int:
        return len(self.BE)

    @property
    def d(self) -> int:
        return 1 + len(self.BE)


def scenarios(I: Instance):
    """M1 scenario set: independent symmetric two-point shocks, all sign combinations, equal weights."""
    sizes = list(I.sf) + [I.sA] + list(I.sE)
    out = []
    for signs in product((1, -1), repeat=len(sizes)):
        z = [s * x for s, x in zip(signs, sizes)]
        zf, zA, zE = z[:2], z[2], z[3:]
        xi = [I.BA[0] * zf[0] + I.BA[1] * zf[1] + zA] + \
             [I.BE[j][0] * zf[0] + I.BE[j][1] * zf[1] + zE[j] for j in range(I.n)]
        out.append((Fr(1, 2 ** len(sizes)), zf, xi))
    return out


def mean_vector(I: Instance, lam=None, alpha=None):
    lam = I.lam if lam is None else lam
    alpha = I.alpha if alpha is None else alpha
    return [I.BA[0] * lam[0] + I.BA[1] * lam[1] + alpha] + \
           [I.BE[j][0] * lam[0] + I.BE[j][1] * lam[1] - I.cE[j] for j in range(I.n)]


def sigma_from_scenarios(I: Instance):
    d = I.d
    S = [[Fr(0)] * d for _ in range(d)]
    for q, _, xi in scenarios(I):
        for i in range(d):
            for j in range(d):
                S[i][j] += q * xi[i] * xi[j]
    return S


def sigma_formula(I: Instance):
    """B Sf B' + D, with Sf = diag(sf^2) and D = diag(sA^2, sE^2)."""
    rows = [I.BA] + list(I.BE)
    res = [I.sA] + list(I.sE)
    d = I.d
    return [[sum(rows[i][k] * rows[j][k] * I.sf[k] ** 2 for k in range(2)) + (res[i] ** 2 if i == j else 0)
             for j in range(d)] for i in range(d)]


def check_instance(I: Instance) -> list[str]:
    """M1 admissibility of the instance data, checked exactly. Empty list = admissible."""
    errs = []
    if sigma_from_scenarios(I) != sigma_formula(I):
        errs.append("scenario covariance differs from B Sf B' + D")
    mu = mean_vector(I)
    for _, zf, xi in scenarios(I):
        for i in range(I.d):
            if 1 + mu[i] + xi[i] <= 0:
                errs.append("gross return not strictly positive in some scenario")
                break
    if any(x < 0 for x in I.w0) or I.k0 < 0 or sum(I.w0) + I.k0 != 1:
        errs.append("pre-trade positions are not a funded long-only allocation")
    if any(not (0 <= k < 1) for k in I.kappa):
        errs.append("kappa outside [0, 1)")
    if any(not (0 <= w <= b <= 1) for w, b in zip(I.w0, I.wbar)):
        errs.append("position limits violated or outside [0, 1]")
    if any(c < 0 for c in I.cE) or I.gamma < 0:
        errs.append("negative drag or risk coefficient")
    return errs


def _solve_linear(A, b, exact: bool):
    """Gaussian elimination; returns the solution or None if singular."""
    n = len(A)
    M = [list(A[i]) + [b[i]] for i in range(n)]
    for c in range(n):
        if exact:
            p = next((r for r in range(c, n) if M[r][c] != 0), None)
        else:
            p = max(range(c, n), key=lambda r: abs(M[r][c]))
            scale = max(1.0, max(abs(x) for row in M for x in row[:n]))
            if abs(M[p][c]) <= 1e-13 * scale:
                p = None
        if p is None:
            return None
        M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]


def objective(I: Instance, S, mu, w):
    d = I.d
    quad = sum(w[i] * S[i][j] * w[j] for i in range(d) for j in range(d))
    return sum(mu[i] * w[i] for i in range(d)) - I.gamma / 2 * quad - \
        sum(I.kappa[i] * abs(w[i] - I.w0[i]) for i in range(d))


def feasible(I: Instance, w, tol=0):
    d = I.d
    if any(w[i] < -tol or w[i] > I.wbar[i] + tol for i in range(d)):
        return False
    v = [w[i] - I.w0[i] for i in range(d)]
    return sum(v) + sum(I.kappa[i] * abs(v[i]) for i in range(d)) <= I.k0 + tol


def solve(I: Instance, cls: str = "F", exact: bool = True, S=None, mu=None):
    """Return (value, optimal point, list of distinct optimal candidates) for class F, E or N."""
    conv = (lambda x: Fr(x)) if exact else float
    d = I.d
    S = [[conv(x) for x in row] for row in (S if S is not None else sigma_formula(I))]
    mu = [conv(x) for x in (mu if mu is not None else mean_vector(I))]
    g, kap = conv(I.gamma), [conv(x) for x in I.kappa]
    w0, wbar, k0 = [conv(x) for x in I.w0], [conv(x) for x in I.wbar], conv(I.k0)
    Ic = Instance(I.BA, I.BE, I.sf, I.sA, I.sE, I.lam, I.alpha, I.cE, g, tuple(kap), tuple(w0), k0,
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
    best, best_w, optima = None, None, []
    seen = set()
    for s in product((1, -1), repeat=d):
        lin = [mu[i] - kap[i] * s[i] for i in range(d)]
        c = [1 + kap[i] * s[i] for i in range(d)]
        for fix in product(*opts):
            F = [i for i in range(d) if fix[i] is None]
            for beq in ((False, True) if F else (False,)):
                m = len(F)
                rhs_fix = [lin[i] - sum(H[i][j] * fix[j] for j in range(d) if fix[j] is not None) for i in F]
                if beq:
                    A = [[H[F[a]][F[b]] for b in range(m)] + [c[F[a]]] for a in range(m)]
                    A.append([c[F[b]] for b in range(m)] + [conv(0)])
                    brhs = k0 + sum(c[i] * w0[i] for i in range(d)) - \
                        sum(c[j] * fix[j] for j in range(d) if fix[j] is not None)
                    sol = _solve_linear(A, rhs_fix + [brhs], exact)
                else:
                    A = [[H[F[a]][F[b]] for b in range(m)] for a in range(m)]
                    sol = _solve_linear(A, rhs_fix, exact) if m else []
                if sol is None:
                    continue
                w = [fix[i] for i in range(d)]
                for a, i in enumerate(F):
                    w[i] = sol[a]
                if any(s[i] * (w[i] - w0[i]) < -tol for i in range(d)):
                    continue
                if not feasible(Ic, w, tol):
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


def positive_definite(S) -> bool:
    """Exact test by leading principal minors (Sylvester)."""
    d = len(S)
    for k in range(1, d + 1):
        M = [[Fr(S[i][j]) for j in range(k)] for i in range(k)]
        det = Fr(1)
        for c in range(k):
            p = next((r for r in range(c, k) if M[r][c] != 0), None)
            if p is None:
                return False
            if p != c:
                M[c], M[p] = M[p], M[c]
                det = -det
            det *= M[c][c]
            for r in range(c + 1, k):
                f = M[r][c] / M[c][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
        if det <= 0:
            return False
    return True
