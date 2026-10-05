"""The M8 harness extended to N funds, M ETFs and K factors (preparation, not an experiment; PM's note
2026-09-30-exp055-056). harness.py's model with the instrument index widened (claim 048's setting, M7's finite-law variant):

Parameters theta = (lambda in R^K, alpha in R^N) drawn once from a finite law; shocks z = (f in R^K, e_A in R^N, e_E in R^M)
from a finite centred law. Excess returns y = G theta + d + L z with G = [[B^A, I_N], [B^E, 0]], d = (0, -c^E),
L = [[B^A, I_N, 0], [B^E, 0, I_M]]. The manager observes y (the instruments' returns) and runs the linear filter;
mu_t = G m_t + d, Sigma_t = G P_t G' + R. Each review scores mu' x - (gamma/2) x' Sigma x - C(u) with directional rates per
instrument, caps, the funded budget h^+ = h^- - 1'u - C(u) >= 0, marking x^-_{t+1} = x^+_t o (1 + y), h^-_{t+1} = h^+_t.

The solver is harness.py's: one convex program over the tree of public histories (CLARABEL, objective scaled by 1e4).
It also returns tomorrow's incumbent values from the duals of the marking constraints: s_1(z') = dV/dx^-_1 at each
state (claim 044's s_{1,i} = eta_1 + (1 + eta_1) t_{1,i}), so S_i = beta E[g_i s_{1,i}] for the solver's admissible family.
Instruments are ordered funds first, then ETFs. With N = M = K = 1 this is harness.Model (validate_n.py checks it).

M9 (D24; model/SPEC.md M9 on mathb/claim114-d24-target-move at eb786cb5): the latent means move between reviews,
theta_{t+1} = Phi theta_t + (I - Phi) theta_bar + eta_{t+1}, eta centred with covariance Q, independent of theta_0 and z.
Returns over (t, t+1] carry theta_t. The filter updates with y_{t+1} and then predicts with Phi, Q:
m_{t+1} = Phi (m_t + K_t nu_{t+1}) + (I - Phi) theta_bar, P_{t+1} = Phi P^u_t Phi' + Q. On the tree, eta enters the true
law of y_{t+2} and later; with T = 2 only the filter changes. Phi = I, Q = 0 (the defaults) is M8 (validate_m9.py).
"""
import itertools
from dataclasses import dataclass, field

import cvxpy as cp
import numpy as np

SCALE = 1e4
OPT = dict(tol_gap_abs=1e-12, tol_gap_rel=1e-10, tol_feas=1e-10, max_iter=500)


@dataclass
class ModelN:
    BA: np.ndarray                  # N x K fund loadings
    BE: np.ndarray                  # M x K ETF loadings
    kp: np.ndarray                  # purchase rates, length N + M
    km: np.ndarray                  # sale rates
    cap: np.ndarray                 # caps (np.inf allowed)
    cE: np.ndarray = None           # ETF drags, length M
    gamma: float = 5.0
    beta: float = 1.0
    theta_atoms: list = field(default_factory=list)   # each of length K + N: (lambda, alpha)
    theta_probs: list = field(default_factory=list)
    z_atoms: list = field(default_factory=list)       # each of length K + N + M: (f, e_A, e_E)
    z_probs: list = field(default_factory=list)
    Phi: np.ndarray = None          # M9: diagonal persistence over theta = (lambda, alpha); None = I (M8)
    Q: np.ndarray = None            # M9: state-noise covariance; None = 0
    theta_bar: np.ndarray = None    # M9: long-run mean; None = m_0
    eta_atoms: list = None          # M9: finite centred law of eta with covariance Q (None: a point at 0)
    eta_probs: list = None
    observe_factor: bool = False    # M9/M8's observation y = (f, r^A, r^E); default observes the instruments' returns only

    def __post_init__(self):
        self.BA = np.atleast_2d(np.asarray(self.BA, float)); self.BE = np.atleast_2d(np.asarray(self.BE, float))
        self.N, self.K = self.BA.shape; self.M = self.BE.shape[0]; self.n = self.N + self.M
        self.cE = np.zeros(self.M) if self.cE is None else np.asarray(self.cE, float)
        self.kp, self.km, self.cap = (np.asarray(v, float) for v in (self.kp, self.km, self.cap))
        N, M, K = self.N, self.M, self.K
        self.G = np.block([[self.BA, np.eye(N)], [self.BE, np.zeros((M, N))]])
        self.d = np.concatenate([np.zeros(N), -self.cE])
        self.L = np.block([[self.BA, np.eye(N), np.zeros((N, M))], [self.BE, np.zeros((M, N)), np.eye(M)]])
        th, pt = np.array(self.theta_atoms, float), np.array(self.theta_probs, float)
        self.m0 = pt @ th; self.P0 = (th - self.m0).T @ np.diag(pt) @ (th - self.m0)
        za, pz = np.array(self.z_atoms, float), np.array(self.z_probs, float)
        assert abs(pz @ za).max() < 1e-12, "the shock law must be centred"
        self.Sz = za.T @ np.diag(pz) @ za
        self.R = self.L @ self.Sz @ self.L.T
        if self.observe_factor:          # y = (f, r): H = [[I_K, 0]; G], d = (0, d), L = [[I_K, 0, 0]; L]
            self.Ho = np.vstack([np.hstack([np.eye(K), np.zeros((K, N))]), self.G]); self.do = np.concatenate([np.zeros(K), self.d])
            self.Lo = np.vstack([np.hstack([np.eye(K), np.zeros((K, N + M))]), self.L])
        else:
            self.Ho, self.do, self.Lo = self.G, self.d, self.L
        self.Ro = self.Lo @ self.Sz @ self.Lo.T
        d = len(self.m0)
        self.Phi = np.eye(d) if self.Phi is None else np.atleast_2d(np.asarray(self.Phi, float))
        self.Q = np.zeros((d, d)) if self.Q is None else np.atleast_2d(np.asarray(self.Q, float))
        self.theta_bar = self.m0.copy() if self.theta_bar is None else np.asarray(self.theta_bar, float)
        if self.eta_atoms is None:
            self.eta_atoms, self.eta_probs = [np.zeros(d)], [1.0]
        ea, pe = np.array(self.eta_atoms, float), np.array(self.eta_probs, float)
        assert abs(pe @ ea).max() < 1e-12 and np.allclose(ea.T @ np.diag(pe) @ ea, self.Q), "eta's law must be centred with covariance Q"

    def P(self, t):
        """The filter's error covariance of theta_t given y_1..y_t (M9: update, then predict with Phi and Q)."""
        P = self.P0.copy()
        for _ in range(t):
            S = self.Ho @ P @ self.Ho.T + self.Ro
            Pu = P - P @ self.Ho.T @ np.linalg.pinv(S) @ self.Ho @ P
            P = self.Phi @ Pu @ self.Phi.T + self.Q
        return P

    def moments(self, t, m):
        return self.G @ m + self.d, self.G @ self.P(t) @ self.G.T + self.R

    def factor_cov(self, t):
        """Sigma~_{f,t} = Sigma_f + P^lambda_t, the factor block of the predictive covariance (claim 048's)."""
        K = self.K
        return self.Sz[:K, :K] + self.P(t)[:K, :K]

    def update(self, t, m, y):
        """m_{t+1} from m_t and y_{t+1}: the update, then M9's predict step (the identity when Phi = I, theta_bar = m_0)."""
        P = self.P(t); S = self.Ho @ P @ self.Ho.T + self.Ro
        mu = m + P @ self.Ho.T @ np.linalg.pinv(S) @ (y - self.Ho @ m - self.do)
        return self.Phi @ mu + (np.eye(len(m)) - self.Phi) @ self.theta_bar

    def tree(self, T=2):
        levels = [[dict(key=(), prob=1.0, m=self.m0.copy(), g=None, parent=None)]]
        paths = []
        I = np.eye(len(self.m0))
        for ti, th in enumerate(np.array(self.theta_atoms, float)):
            for zs in itertools.product(range(len(self.z_atoms)), repeat=T - 1):
                for es in itertools.product(range(len(self.eta_atoms)), repeat=max(T - 2, 0)):   # M9: eta_1..eta_{T-2} move theta
                    pr = self.theta_probs[ti] * np.prod([self.z_probs[k] for k in zs]) * np.prod([self.eta_probs[j] for j in es])
                    ys, rs, thv = [], [], th.copy()
                    for s_, k in enumerate(zs):
                        z = np.array(self.z_atoms[k], float)
                        ys.append(self.Ho @ thv + self.do + self.Lo @ z); rs.append(self.G @ thv + self.d + self.L @ z)
                        if s_ < len(es):
                            thv = self.Phi @ thv + (I - self.Phi) @ self.theta_bar + np.array(self.eta_atoms[es[s_]], float)
                    paths.append((pr, ys, rs))
        for t in range(1, T):
            idx = {}; lev = []
            for pr, ys, rs in paths:
                key = tuple(np.round(np.concatenate(ys[:t]), 12))
                if key not in idx:
                    pkey = tuple(np.round(np.concatenate(ys[:t - 1]), 12)) if t > 1 else ()
                    parent = next(i for i, nd in enumerate(levels[t - 1]) if nd["key"] == pkey)
                    m = self.update(t - 1, levels[t - 1][parent]["m"], ys[t - 1])
                    idx[key] = len(lev); lev.append(dict(key=key, prob=0.0, m=m, g=1.0 + rs[t - 1], parent=parent))
                lev[idx[key]]["prob"] += pr
            levels.append(lev)
        return levels

    def cost(self, u):
        return float(self.kp @ np.maximum(u, 0) + self.km @ np.maximum(-u, 0))

    def solve(self, x0, h0, T=2, budget=True, fix_root=None, frozen=(), budget_t=None):
        """The exact T-review program from pre-trade holdings x0 and cash h0. fix_root = {instrument: value} fixes root
        holdings; frozen lists instruments that never trade (claim 114 3a's fixed ETF). Returns holdings, cash, the budget multipliers eta[t][node], the incumbent values s[t][node] (t >= 1),
        and the value."""
        levels = self.tree(T); cons = []; obj = 0
        X, Hs, B, Mk = [], [], [], []
        for t, lev in enumerate(levels):
            Xt, Ht, Bt, Mt = [], [], [], []
            for nd in lev:
                x = cp.Variable(self.n); up, dn = cp.Variable(self.n, nonneg=True), cp.Variable(self.n, nonneg=True)
                xm = np.asarray(x0, float) if t == 0 else cp.multiply(X[t - 1][nd["parent"]], nd["g"])
                hm = h0 if t == 0 else Hs[t - 1][nd["parent"]]
                C = self.kp @ up + self.km @ dn
                h = hm - cp.sum(up - dn) - C
                mk = x - xm == up - dn
                cons += [mk, x >= 0]
                fin = np.isfinite(self.cap)
                if fin.any():
                    cons.append(x[np.where(fin)[0]] <= self.cap[fin])
                if budget and (budget_t is None or t in budget_t):     # D26's policy 2: the budget at the listed reviews only
                    bc = h >= 0; cons.append(bc); Bt.append(bc)
                if fix_root is not None and t == 0:
                    for i, v in fix_root.items():
                        cons.append(x[i] == v)
                for i in frozen:
                    cons += [up[i] == 0, dn[i] == 0]
                mu, S = self.moments(t, nd["m"])
                obj += nd["prob"] * self.beta ** t * (mu @ x - 0.5 * self.gamma * cp.quad_form(x, cp.psd_wrap(S)) - C)
                Xt.append(x); Ht.append(h); Mt.append(mk)
            X.append(Xt); Hs.append(Ht); B.append(Bt); Mk.append(Mt)
        pr = cp.Problem(cp.Maximize(SCALE * obj), cons); pr.solve(solver="CLARABEL", **OPT)
        w = lambda t, nd: SCALE * nd["prob"] * self.beta ** t
        eta = [[float(b.dual_value) / w(t, nd) for b, nd in zip(Bt, lev)] if Bt else None for t, (Bt, lev) in enumerate(zip(B, levels))] if budget else None
        # the marking constraint x - xm == up - dn: its dual is the value of one more pre-trade unit (sign fixed by validate_n.py)
        s = [None] + [[np.asarray(mk.dual_value, float) / w(t, nd) for mk, nd in zip(Mt, lev)] for t, (Mt, lev) in enumerate(zip(Mk, levels)) if t >= 1]
        self.last_stats = dict(status=pr.status, solve_time=pr.solver_stats.solve_time, iters=pr.solver_stats.num_iters, n_vars=sum(v.size for v in pr.variables()))
        return dict(status=pr.status, value=pr.value / SCALE if pr.value is not None else None, levels=levels,
                    x=[[np.array(v.value) for v in Xt] for Xt in X], h=[[float(v.value) for v in Ht] for Ht in Hs], eta=eta, s=s)

    def one_review(self, mu, S, xm, hm, budget=True, frozen=()):
        """Claim 110's one-review problem at given moments: holdings, the budget multiplier, leftover cash."""
        x = cp.Variable(self.n); up, dn = cp.Variable(self.n, nonneg=True), cp.Variable(self.n, nonneg=True)
        C = self.kp @ up + self.km @ dn
        cons = [x - xm == up - dn, x >= 0] + [c for i in frozen for c in (up[i] == 0, dn[i] == 0)]
        fin = np.isfinite(self.cap)
        if fin.any():
            cons.append(x[np.where(fin)[0]] <= self.cap[fin])
        bc = hm - cp.sum(up - dn) - C >= 0
        if budget:
            cons.append(bc)
        cp.Problem(cp.Maximize(SCALE * (mu @ x - 0.5 * self.gamma * cp.quad_form(x, cp.psd_wrap(S)) - C)), cons).solve(solver="CLARABEL", **OPT)
        xv = np.array(x.value)
        return xv, (float(bc.dual_value) / SCALE if budget else 0.0), float(hm - np.sum(xv - xm) - self.cost(xv - xm))


def two_point(sds):
    """The product of two-point laws +- sd over the coordinates with sd > 0 (others fixed at 0)."""
    sds = np.asarray(sds, float); act = np.where(sds > 0)[0]
    atoms = []
    for signs in itertools.product((1, -1), repeat=len(act)):
        a = np.zeros(len(sds)); a[act] = np.array(signs) * sds[act]; atoms.append(a)
    return atoms, [1.0 / len(atoms)] * len(atoms)


def axis_law(sds):
    """A finite centred law with covariance diag(sds^2) on 2d atoms, +- sqrt(d) sd_i on each active coordinate (d active)."""
    sds = np.asarray(sds, float); act = np.where(sds > 0)[0]; d = len(act)
    if d == 0:
        return [np.zeros(len(sds))], [1.0]
    atoms = []
    for i in act:
        for sgn in (1, -1):
            a = np.zeros(len(sds)); a[i] = sgn * np.sqrt(d) * sds[i]; atoms.append(a)
    return atoms, [1.0 / (2 * d)] * (2 * d)


def mn_model(BA, BE, lam, alpha, premium_sd, sigma_f, sigma_A, alpha_sd=None, alpha_revision_var=None, sigma_E=None, cE=None,
             gamma=5.0, beta=1.0, kp=None, km=None, cap=None, phi=None, q=None, theta_bar=None, law="product", observe_factor=False):
    """M8's finite-law variant with N funds, M ETFs and K factors: two points per parameter coordinate (m_0 +- sqrt(P_0)),
    two points per shock coordinate (+- sd). alpha_sd or alpha_revision_var (per fund) sets the alpha prior as in
    harness.m8_model. law = "axis" uses axis_law for theta, z and eta instead (2d atoms per block, the same moments;
    D26's larger menus). observe_factor = True is M9's observation (f, r^A, r^E). M9: phi and q (per coordinate of theta = (lambda, alpha), length K + N, or scalars) and theta_bar
    (default the prior mean); eta's law is two points per coordinate, +- sqrt(q)."""
    BA = np.atleast_2d(np.asarray(BA, float)); BE = np.atleast_2d(np.asarray(BE, float)); N, K = BA.shape; M = BE.shape[0]
    sigma_A = np.broadcast_to(np.asarray(sigma_A, float), (N,))
    if alpha_sd is not None:
        pa = np.broadcast_to(np.asarray(alpha_sd, float), (N,)) ** 2
    else:
        V = np.broadcast_to(np.asarray(alpha_revision_var, float), (N,)); s2 = sigma_A ** 2
        pa = (V + np.sqrt(V ** 2 + 4 * V * s2)) / 2
    th_sd = np.concatenate([np.broadcast_to(np.asarray(premium_sd, float), (K,)), np.sqrt(pa)])
    th_c = np.concatenate([np.broadcast_to(np.asarray(lam, float), (K,)), np.broadcast_to(np.asarray(alpha, float), (N,))])
    lawf = axis_law if law == "axis" else two_point
    dev, pth = lawf(th_sd)
    sE = np.zeros(M) if sigma_E is None else np.broadcast_to(np.asarray(sigma_E, float), (M,))
    za, pz = lawf(np.concatenate([np.broadcast_to(np.asarray(sigma_f, float), (K,)), sigma_A, sE]))
    d = K + N
    Phi = None if phi is None else np.diag(np.broadcast_to(np.asarray(phi, float), (d,)))
    qv = None if q is None else np.broadcast_to(np.asarray(q, float), (d,))
    ea, pe = (None, None) if qv is None else lawf(np.sqrt(qv))
    return ModelN(BA=BA, BE=BE, kp=kp, km=km, cap=cap, cE=cE, gamma=gamma, beta=beta,
                  theta_atoms=[th_c + d_ for d_ in dev], theta_probs=pth, z_atoms=za, z_probs=pz,
                  Phi=Phi, Q=None if qv is None else np.diag(qv), theta_bar=theta_bar, eta_atoms=ea, eta_probs=pe, observe_factor=observe_factor)
