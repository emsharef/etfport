"""Finite checks for claim 019; not its proof.

Run: uv run python checks/019/check.py

Part A (gamma = 0, random M4 designs with one or two ETFs, directional costs,
caps, nonzero incumbents and small cash): the face sets Vert(E) and Vert(F)
are enumerated exactly in rational arithmetic from the cost-sign cells, and
their maxima are compared with an independent floating-point LP over the
lifted (purchase, sale) formulation. The ellipsoidal closed form of the
whole-class certificate is compared with direct evaluation of the true
advantage at sampled and at the worst parameters. The lexicographic plug-in
optimizer is checked to lie in Vert(F). For one ETF, Vert(E) is checked to
be the three holdings named in the claim.

Part B (gamma > 0, claim 017's family): for every finite comparator set of
size m the curvature deficit is at least s^2/(2(m+1)^2) somewhere in the
domain, and the finite-face contrast certifies an action that is strictly
worse than the whole ETF class.

These are finite checks of random and fixed instances, not the proof.
"""
from fractions import Fraction as Fr
from itertools import combinations, product
import random
import sys

import numpy as np
from scipy.optimize import linprog

TOL = 1e-8


# ---------------------------------------------------------------- exact algebra
def solve_exact(rows, rhs):
    """Solve a square rational system; None if singular."""
    m = len(rows)
    M = [list(r) + [b] for r, b in zip(rows, rhs)]
    for col in range(m):
        piv = next((r for r in range(col, m) if M[r][col] != 0), None)
        if piv is None:
            return None
        M[col], M[piv] = M[piv], M[col]
        pv = M[col][col]
        M[col] = [x / pv for x in M[col]]
        for r in range(m):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [x - f * y for x, y in zip(M[r], M[col])]
    return [M[r][m] for r in range(m)]


def extreme_points(G, h):
    """Exact extreme points of {x: G x <= h} (dimension = len(G[0]))."""
    m = len(G[0])
    pts = set()
    for idx in combinations(range(len(G)), m):
        x = solve_exact([G[i] for i in idx], [h[i] for i in idx])
        if x is None:
            continue
        if all(sum(g * xi for g, xi in zip(G[i], x)) <= h[i] for i in range(len(G))):
            pts.add(tuple(x))
    return sorted(pts)


# ---------------------------------------------------------------- M4 designs
class Design:
    """gamma = 0 M4 design: caps, incumbent, cash, directional rates, loadings, drag."""

    def __init__(self, rng, n):
        self.n = n
        self.cap = [Fr(rng.randint(2, 6), 4) for _ in range(1 + n)]
        self.inc = [c * Fr(rng.choice([0, 1, 2, 3, 4]), 4) for c in self.cap]
        self.cash = Fr(rng.choice([0, 1, 2, 5, 10, 20]), 20)
        self.kp = [Fr(rng.choice([0, 1, 5, 20, 50]), 1000) for _ in range(1 + n)]
        self.km = [Fr(rng.choice([0, 1, 5, 20, 50]), 1000) for _ in range(1 + n)]
        self.BA = [Fr(rng.randint(-4, 4), 4) for _ in range(2)]
        self.BE = [[Fr(rng.randint(-4, 4), 4) for _ in range(2)] for _ in range(n)]
        self.drag = [Fr(rng.randint(-5, 5), 1000) for _ in range(n)]

    # A w = (b(w), a): a 3-by-(1+n) matrix.
    def A(self):
        cols = [[self.BA[0], self.BA[1], Fr(1)]] + [[b[0], b[1], Fr(0)] for b in self.BE]
        return [[cols[j][i] for j in range(1 + self.n)] for i in range(3)]

    def tau(self, w):
        return sum(self.kp[i] * max(w[i] - self.inc[i], 0) + self.km[i] * max(self.inc[i] - w[i], 0)
                   for i in range(1 + self.n))

    def cashafter(self, w):
        return self.cash - sum(w[i] - self.inc[i] for i in range(1 + self.n)) - self.tau(w)

    def feasible(self, w):
        return all(0 <= w[i] <= self.cap[i] for i in range(1 + self.n)) and self.cashafter(w) >= 0

    def Q(self, w, theta):
        A = self.A()
        Aw = [sum(A[i][j] * w[j] for j in range(1 + self.n)) for i in range(3)]
        return (sum(theta[i] * Aw[i] for i in range(3))
                - sum(self.drag[j] * w[1 + j] for j in range(self.n)) - self.tau(w))

    def cell(self, sigma, etf_only):
        """Halfspace description G x <= h of a cost-sign cell.

        etf_only: x = p in R^n with a = a^-; otherwise x = w in R^{1+n}."""
        idx = list(range(1, 1 + self.n)) if etf_only else list(range(1 + self.n))
        m = len(idx)
        G, h = [], []
        for k, i in enumerate(idx):
            e = [Fr(0)] * m
            e[k] = Fr(1)
            G.append(e); h.append(self.cap[i])
            G.append([-x for x in e]); h.append(Fr(0))
            G.append([-sigma[k] * x for x in e]); h.append(-sigma[k] * self.inc[i])
        coef = [Fr(1) + (self.kp[i] if sigma[k] == 1 else -self.km[i]) for k, i in enumerate(idx)]
        G.append(coef)
        h.append(self.cash + sum(c * self.inc[i] for c, i in zip(coef, idx)))
        return G, h

    def faces(self, etf_only):
        m = self.n if etf_only else 1 + self.n
        pts = set()
        for sigma in product((1, -1), repeat=m):
            G, h = self.cell(sigma, etf_only)
            for x in extreme_points(G, h):
                w = (self.inc[0],) + tuple(x) if etf_only else tuple(x)
                assert self.feasible(w)
                pts.add(w)
        return sorted(pts)

    def lp_max(self, theta, etf_only):
        """Independent float LP: lifted purchase/sale variables."""
        n1 = 1 + self.n
        A = np.array(self.A(), dtype=float)
        th = np.array(theta, dtype=float)
        lin = th @ A
        lin[1:] -= np.array(self.drag, dtype=float)
        # variables: w (n1), yplus (n1), yminus (n1)
        c = np.concatenate([-lin, np.array(self.kp, float), np.array(self.km, float)])
        Aeq = np.hstack([np.eye(n1), -np.eye(n1), np.eye(n1)])
        beq = np.array(self.inc, float)
        Aub = np.concatenate([np.zeros(n1), 1 + np.array(self.kp, float), -1 + np.array(self.km, float)])[None, :]
        bub = np.array([float(self.cash)])
        bounds = [(0.0, float(self.cap[i])) for i in range(n1)] + [(0, None)] * (2 * n1)
        if etf_only:
            bounds[0] = (float(self.inc[0]), float(self.inc[0]))
        res = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=bounds, method="highs")
        assert res.status == 0, res.message
        return -res.fun, res.x[:n1]

    def lex_min_maximizer_lifted(self, theta):
        """Exact lexicographic minimum of the full maximizer set, computed on a
        different polytope: the lifted purchase/sale formulation y=(yplus,yminus)
        with w = w^- + yplus - yminus. Its maximizer set projects onto F's, and a
        lexicographic minimum over a polytope is one of its vertices, so the
        minimum over projected lifted vertices is the exact answer."""
        n1 = 1 + self.n
        m = 2 * n1
        G, h = [], []
        for k in range(m):                      # y >= 0
            e = [Fr(0)] * m; e[k] = Fr(-1); G.append(e); h.append(Fr(0))
        for i in range(n1):                     # 0 <= inc + yplus - yminus <= cap
            e = [Fr(0)] * m; e[i] = Fr(1); e[n1 + i] = Fr(-1)
            G.append(e); h.append(self.cap[i] - self.inc[i])
            G.append([-x for x in e]); h.append(self.inc[i])
        e = [Fr(1) + self.kp[i] for i in range(n1)] + [Fr(-1) + self.km[i] for i in range(n1)]
        G.append(e); h.append(self.cash)        # cash after costs >= 0
        A = self.A()
        best, argbest = None, []
        for y in extreme_points(G, h):
            w = tuple(self.inc[i] + y[i] - y[n1 + i] for i in range(n1))
            Aw = [sum(A[r][j] * w[j] for j in range(n1)) for r in range(3)]
            val = (sum(theta[r] * Aw[r] for r in range(3))
                   - sum(self.drag[j] * w[1 + j] for j in range(self.n))
                   - sum(self.kp[i] * y[i] + self.km[i] * y[n1 + i] for i in range(n1)))
            if best is None or val > best:
                best, argbest = val, [w]
            elif val == best:
                argbest.append(w)
        return best, min(argbest)


def part_a():
    rng = random.Random(19)
    n_designs = 0
    for trial in range(120):
        n = 1 + (trial % 2)
        d = Design(rng, n)
        VE, VF = d.faces(True), d.faces(False)
        assert len(VE) <= 2 ** n * {1: 4, 2: 21}[n]
        assert len(VF) <= 2 ** (n + 1) * {1: 21, 2: 120}[n]
        if n == 1:
            p_lo, p_inc, cap = Fr(0), d.inc[1], d.cap[1]
            p_hi = p_inc + min(cap - p_inc, d.cash / (1 + d.kp[1]))
            assert set(VE) == {(d.inc[0], p) for p in (p_lo, p_inc, p_hi)}, (VE, p_hi)
        for _ in range(3):
            theta = [Fr(rng.randint(-8, 8), 16) for _ in range(3)]
            # 1. finite face maxima equal the LP maxima over the whole classes.
            vE = max(d.Q(v, theta) for v in VE)
            vF = max(d.Q(u, theta) for u in VF)
            lpE, _ = d.lp_max(theta, True)
            lpF, _ = d.lp_max(theta, False)
            assert abs(float(vE) - lpE) < TOL and abs(float(vF) - lpF) < TOL, (vE, lpE, vF, lpF)
            # 2. the lexicographic plug-in optimizer is a face of F.
            v_lift, lex_lift = d.lex_min_maximizer_lifted(theta)
            maximizers = [u for u in VF if d.Q(u, theta) == vF]
            lex = min(maximizers)
            assert v_lift == vF and lex_lift == lex and lex in VF, (lex, lex_lift)
        # 3. ellipsoidal closed form of the whole-class certificate.
        theta_hat = np.array([rng.uniform(-0.5, 0.5) for _ in range(3)])
        J = np.array([[rng.uniform(-0.05, 0.05) for _ in range(3)] for _ in range(3)])
        if trial % 3 == 0:
            J[:, 2] = 0.0  # singular error covariance
        r = rng.choice([0.5, 1.0, 2.0])
        A = np.array(d.A(), dtype=float)
        w = rng.choice(VF)
        wf = np.array(w, float)

        def adv(theta):
            th = [Fr(float(t)).limit_denominator(10 ** 9) for t in theta]
            vE_here, _ = d.lp_max(th, True)
            return float(d.Q(w, th)) - vE_here

        terms = []
        for v in VE:
            dvec = A @ (wf - np.array(v, float))
            m_hat = adv_pair = float(d.Q(w, [Fr(float(t)).limit_denominator(10 ** 9) for t in theta_hat])
                                     - d.Q(v, [Fr(float(t)).limit_denominator(10 ** 9) for t in theta_hat]))
            terms.append((m_hat - r * np.linalg.norm(J.T @ dvec), v, dvec))
        ell, vstar, dstar = min(terms, key=lambda t: t[0])
        # sampled parameters in the error set never fall below ell
        for _ in range(40):
            y = np.array([rng.gauss(0, 1) for _ in range(3)])
            y *= r * rng.uniform(0, 1) ** (1 / 3) / np.linalg.norm(y)
            assert adv(theta_hat - J @ y) >= ell - 1e-6
        # the worst parameter attains it
        nrm = np.linalg.norm(J.T @ dstar)
        if nrm > 1e-12:
            ystar = r * (J.T @ dstar) / nrm
            assert abs(adv(theta_hat - J @ ystar) - ell) < 1e-6
        n_designs += 1
    print(f"part A: {n_designs} random designs passed")


# ---------------------------------------------------------------- claim 017 family
def part_b():
    s = Fr(1, 100)
    lo, hi = Fr(1, 4) - s, Fr(1, 4) + s
    rng = random.Random(17)
    for m in range(1, 9):
        for kind in ("spaced", "random"):
            if kind == "spaced":
                S = [lo + (hi - lo) * Fr(2 * i + 1, 2 * m) for i in range(m)]
            else:
                S = sorted(lo + (hi - lo) * Fr(rng.randint(0, 1000), 1000) for _ in range(m))
            # worst lambda_2: an endpoint or a midpoint between consecutive comparators
            cands = [lo, hi] + [(S[i] + S[i + 1]) / 2 for i in range(m - 1)]
            cands = [c for c in cands if lo <= c <= hi]
            lam2 = max(cands, key=lambda c: min(abs(c - p) for p in S))
            deficit = min((lam2 - p) ** 2 / 2 for p in S)   # V_E - max_S Q, exactly
            assert deficit >= s ** 2 / (2 * (m + 1) ** 2), (m, kind, deficit)
            # the finite-face contrast certifies a strictly worse action at x = 0
            a = s / (2 * (m + 1))
            adv_w = -a ** 2                      # a x - a^2 - (p - lambda_2)^2/2 at x=0, p=lambda_2
            finite_contrast = adv_w + deficit
            assert finite_contrast > 0 > adv_w, (m, kind, finite_contrast, adv_w)
            assert a + lam2 <= 1                 # funded, caps one, zero cost
    print("part B: curvature deficit and finite-face over-certification confirmed for m = 1..8")


if __name__ == "__main__":
    part_a()
    part_b()
    print("checks/019: all checks passed")
    sys.exit(0)
