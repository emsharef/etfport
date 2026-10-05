"""D16/D18 harness (preparation, not an experiment; PM's note 2026-09-29-d16-harness): the exact T-review problem for one
fund, one ETF and cash in M7's finite-law variant (model/SPEC.md, M6-M7).

The model. Parameters theta = (lambda, alpha) drawn once from a finite law; shocks z_{t+1} = (f, e_A, e_E) from a finite
centred law, independent across quarters and of theta. Excess returns over cash y = G theta + d + L z with
G = [[b_A, 1], [b_E, 0]], d = (0, -c^E), L = [[b_A, 1, 0], [b_E, 0, 1]]; gross returns 1 + y (cash has gross return 1).
The manager runs M7's linear filter (H = G, R = L Sigma_z L'): P_t deterministic, m_{t+1} = m_t + K_t (y - H m_t - d),
mu_t = G m_t + d, Sigma_t = G P_t G' + R. Review t scores mu_t' x^+ - (gamma/2) x^+' Sigma_t x^+ - C(u), with directional
rates, caps 0 <= x^+ <= bar x, the funded budget h^+ = h^- - 1'u - C(u) >= 0, marking x_{t+1}^- = x_t^+ o (1 + y_{t+1}),
h_{t+1}^- = h_t^+, discount beta, no terminal trade.

The solver. The problem is convex (each review's score is concave, marking is linear, cash enters monotonically), so
the exact dynamic program is one convex program over the tree of public histories: a decision per distinct history
y_1..y_t (non-anticipative), weighted by the true predictive probability of the finite law. This extends experiment
044's one-review program (split trades, the funded budget, CLARABEL with the objective scaled by 1e4) to the tree;
experiment 036's grid DP is the slack-budget special case. The repeated one-review policy re-solves the T = 1 problem at
each node with that node's moments.
"""
import itertools
from dataclasses import dataclass, field

import cvxpy as cp
import numpy as np

SCALE = 1e4
OPT = dict(tol_gap_abs=1e-12, tol_gap_rel=1e-10, tol_feas=1e-10, max_iter=500)


@dataclass
class Model:
    bA: float = 1.0
    bE: float = 1.0
    gamma: float = 5.0
    beta: float = 1.0
    kAp: float = 0.005
    kAm: float = 0.005
    kEp: float = 0.0002
    kEm: float = 0.0002
    capA: float = 0.25
    capE: float = np.inf
    cE: float = 0.0
    theta_atoms: list = field(default_factory=lambda: [(0.015, -0.002), (0.015, 0.002)])   # (lambda, alpha)
    theta_probs: list = field(default_factory=lambda: [0.5, 0.5])
    z_atoms: list = field(default_factory=lambda: [(s1 * 0.08, s2 * 0.02, 0.0) for s1 in (1, -1) for s2 in (1, -1)])  # (f, e_A, e_E)
    z_probs: list = field(default_factory=lambda: [0.25] * 4)
    observe_factor: bool = False          # experiment 050: M8's observation y = (f, r^A, r^E); default observes (r^A, r^E)

    def __post_init__(self):
        self.G = np.array([[self.bA, 1.0], [self.bE, 0.0]]); self.d = np.array([0.0, -self.cE])
        self.L = np.array([[self.bA, 1.0, 0.0], [self.bE, 0.0, 1.0]])
        th, pt = np.array(self.theta_atoms, float), np.array(self.theta_probs, float)
        self.m0 = pt @ th; self.P0 = (th - self.m0).T @ np.diag(pt) @ (th - self.m0)
        za, pz = np.array(self.z_atoms, float), np.array(self.z_probs, float)
        assert abs(pz @ za).max() < 1e-12, "the shock law must be centred"
        self.Sz = za.T @ np.diag(pz) @ za
        self.R = self.L @ self.Sz @ self.L.T
        self.cap = np.array([self.capA, self.capE])
        if self.observe_factor:           # M8: observe (f, r^A, r^E) = H theta + d + L_o z
            self.Ho = np.array([[1.0, 0.0], [self.bA, 1.0], [self.bE, 0.0]]); self.do = np.array([0.0, 0.0, -self.cE])
            self.Lo = np.array([[1.0, 0.0, 0.0], [self.bA, 1.0, 0.0], [self.bE, 0.0, 1.0]]); self.Ro = self.Lo @ self.Sz @ self.Lo.T
        else:
            self.Ho, self.do, self.Lo, self.Ro = self.G, self.d, self.L, self.R

    def P(self, t):
        """Deterministic filter covariance P_t (information form when P_0 is invertible, else the recursion)."""
        P = self.P0.copy()
        for _ in range(t):
            S = self.Ho @ P @ self.Ho.T + self.Ro
            P = P - P @ self.Ho.T @ np.linalg.solve(S, self.Ho @ P)
        return P

    def moments(self, t, m):
        P = self.P(t)
        return self.G @ m + self.d, self.G @ P @ self.G.T + self.R

    def update(self, t, m, y):
        P = self.P(t); S = self.Ho @ P @ self.Ho.T + self.Ro
        return m + P @ self.Ho.T @ np.linalg.solve(S, y - self.Ho @ m - self.do)

    def tree(self, T):
        """Public nodes by review: each node = (history key, prob, m_t, gross returns into it, parent index)."""
        levels = [[dict(key=(), prob=1.0, m=self.m0.copy(), g=None, parent=None)]]
        # joint law of the histories: enumerate (theta, z_1..z_{T-1}) and aggregate by rounded y history
        paths = []
        for (ti, th), in [((i, np.array(a, float)),) for i, a in enumerate(self.theta_atoms)]:
            for zs in itertools.product(range(len(self.z_atoms)), repeat=T - 1):
                pr = self.theta_probs[ti] * np.prod([self.z_probs[k] for k in zs])
                ys = [self.Ho @ th + self.do + self.Lo @ np.array(self.z_atoms[k], float) for k in zs]
                rs = [self.G @ th + self.d + self.L @ np.array(self.z_atoms[k], float) for k in zs]
                paths.append((pr, ys, rs, ti))
        for t in range(1, T):
            idx = {}; lev = []
            for pr, ys, rs, ti in paths:
                key = tuple(np.round(np.concatenate(ys[:t]), 12))
                if key not in idx:
                    pkey = tuple(np.round(np.concatenate(ys[:t - 1]), 12)) if t > 1 else ()
                    parent = next(i for i, nd in enumerate(levels[t - 1]) if nd["key"] == pkey)
                    m = self.update(t - 1, levels[t - 1][parent]["m"], ys[t - 1])
                    idx[key] = len(lev); lev.append(dict(key=key, prob=0.0, m=m, g=1.0 + rs[t - 1], parent=parent, theta_w={}))
                lev[idx[key]]["prob"] += pr
                lev[idx[key]]["theta_w"][ti] = lev[idx[key]]["theta_w"].get(ti, 0.0) + pr      # for the exact posterior (experiment 050)
            levels.append(lev)
        return levels

    def solve(self, x0, h0, T=2, budget=True, frozen_etf=False, fix_root_fund=None, moments_fn=None, budget_t=None):
        """The exact T-review program from pre-trade holdings x0 (fund, ETF) and cash h0. Returns the node decisions and
        the value. frozen_etf fixes the ETF at its marked holding (a validation device)."""
        levels = self.tree(T); cons = []; obj = 0
        X, Hs, B = [], [], []
        for t, lev in enumerate(levels):
            Xt, Ht, Bt = [], [], []
            for nd in lev:
                x = cp.Variable(2); up, dn = cp.Variable(2, nonneg=True), cp.Variable(2, nonneg=True)
                if t == 0:
                    xm, hm = np.asarray(x0, float), h0
                else:
                    xm = cp.multiply(X[t - 1][nd["parent"]], nd["g"]); hm = Hs[t - 1][nd["parent"]]
                C = self.kAp * up[0] + self.kAm * dn[0] + self.kEp * up[1] + self.kEm * dn[1]
                h = hm - cp.sum(up - dn) - C
                cons += [x - xm == up - dn, x >= 0, x[0] <= self.capA]
                if np.isfinite(self.capE):
                    cons.append(x[1] <= self.capE)
                if budget and (budget_t is None or t in budget_t):        # experiment 052: the budget at the listed reviews only
                    bc = h >= 0; cons.append(bc); Bt.append(bc)
                if frozen_etf:
                    cons.append(dn[1] == 0); cons.append(up[1] == 0)
                if fix_root_fund is not None and t == 0:          # experiment 049's reduced point: the root fund holding fixed
                    cons.append(x[0] == fix_root_fund)
                mu, S = moments_fn(t, nd) if moments_fn is not None else self.moments(t, nd["m"])   # experiment 050: another manager's moments
                obj += nd["prob"] * self.beta ** t * (mu @ x - 0.5 * self.gamma * cp.quad_form(x, cp.psd_wrap(S)) - C)
                Xt.append(x); Ht.append(h)
            X.append(Xt); Hs.append(Ht); B.append(Bt)
        pr = cp.Problem(cp.Maximize(SCALE * obj), cons); pr.solve(solver="CLARABEL", **OPT)
        # budget multipliers per node (experiment 047's accessor): dual / (scale x probability x beta^t)
        eta = [[float(b.dual_value) / (SCALE * nd["prob"] * self.beta ** t) for b, nd in zip(Bt, lev)] if Bt else None for t, (Bt, lev) in enumerate(zip(B, levels))] if budget else None
        return dict(status=pr.status, value=pr.value / SCALE if pr.value is not None else None,
                    x=[[np.array(x.value) for x in Xt] for Xt in X], levels=levels, eta=eta,
                    h=[[float(h.value) for h in Ht] for Ht in Hs])

    def myopic_root(self, x0, h0, budget=True):
        """The repeated one-review policy's decision at the root: the T = 1 program."""
        return self.solve(x0, h0, T=1, budget=budget)["x"][0][0]

    def reduced_fund(self, a0, T=2):
        """Claim 107 part 3's reduction (frictionless, fee-free, residual-free ETF; slack bounds): the fund-only program
        with curvature c^res_t = gamma (S_AA - S_AE^2/S_EE) and reduced target a^red_t = (mu_A - rho_t mu_E)/c^res_t."""
        levels = self.tree(T); cons = []; obj = 0; A = []
        for t, lev in enumerate(levels):
            At = []
            for nd in lev:
                a = cp.Variable(); up, dn = cp.Variable(nonneg=True), cp.Variable(nonneg=True)
                am = a0 if t == 0 else A[t - 1][nd["parent"]] * nd["g"][0]
                cons += [a - am == up - dn, a >= 0, a <= self.capA]
                mu, S = self.moments(t, nd["m"])
                rho = S[0, 1] / S[1, 1]; cres = self.gamma * (S[0, 0] - S[0, 1] ** 2 / S[1, 1])
                ared = (mu[0] - rho * mu[1]) / cres
                obj += nd["prob"] * self.beta ** t * (-0.5 * cres * cp.square(a - ared) - self.kAp * up - self.kAm * dn)
                At.append(a)
            A.append(At)
        cp.Problem(cp.Maximize(SCALE * obj), cons).solve(solver="CLARABEL", **OPT)
        return [[float(a.value) for a in At] for At in A]


def m8_model(bA=1.0, bE=1.0, cE=0.0, lam=0.015, alpha=0.0, premium_sd=0.005, alpha_sd=None, alpha_gain=None, alpha_revision_var=None,
             premium_gain=None, premium_revision_var=None, sigma_f=0.08, sigma_A=0.02, sigma_E=0.0, gamma=5.0, beta=1.0,
             etf_rate=0.0002, etf_rate_buy=None, etf_rate_sell=None, fund_rate=None, cost_ratio=None, fund_rate_buy=None, fund_rate_sell=None,
             capA=0.25, capE=np.inf, observe_factor=True):
    """M8's finite-law variant with the revision variance and the cost ratio as direct inputs (PM's D19 note, item 2).
    Parameters: two points per block, m_0 +- sqrt(P_0) (M8's reference); shocks two points, +- sigma (experiment 048's).
    The alpha block's prior variance is set by exactly one of alpha_sd, alpha_gain k (p = k sigma_A^2/(1 - k)) or
    alpha_revision_var V = P_0 - P_1 = p^2/(p + sigma_A^2) (p = (V + sqrt(V^2 + 4 V sigma_A^2))/2); likewise the premium block
    with sigma_f. The fund's rates are fund_rate (both sides), or cost_ratio times the ETF's rates (the fund's purchase rate
    against the ETF's), with each side settable. observe_factor = True is M8's observation (f, r^A, r^E)."""
    def prior_var(sd, gain, V, noise_sd):
        given = [x is not None for x in (sd, gain, V)]
        assert sum(given) == 1, "set exactly one of sd, gain, revision variance"
        if sd is not None:
            return sd ** 2
        s2 = noise_sd ** 2
        if gain is not None:
            return gain * s2 / (1 - gain)
        return (V + np.sqrt(V ** 2 + 4 * V * s2)) / 2
    pa = prior_var(alpha_sd, alpha_gain, alpha_revision_var, sigma_A)
    pl = prior_var(premium_sd if (premium_gain is None and premium_revision_var is None) else None, premium_gain, premium_revision_var, sigma_f)
    kEp = etf_rate if etf_rate_buy is None else etf_rate_buy; kEm = etf_rate if etf_rate_sell is None else etf_rate_sell
    if fund_rate is not None:
        kAp = kAm = fund_rate
    else:
        kAp, kAm = cost_ratio * kEp, cost_ratio * kEm
    kAp = kAp if fund_rate_buy is None else fund_rate_buy; kAm = kAm if fund_rate_sell is None else fund_rate_sell
    za = [(a * sigma_f, b * sigma_A, c * sigma_E) for a in (1, -1) for b in (1, -1) for c in ((1, -1) if sigma_E > 0 else (0,))]
    return Model(bA=bA, bE=bE, cE=cE, gamma=gamma, beta=beta, kAp=kAp, kAm=kAm, kEp=kEp, kEm=kEm, capA=capA, capE=capE,
                 theta_atoms=[(lam + a * np.sqrt(pl), alpha + b * np.sqrt(pa)) for a in (1, -1) for b in (1, -1)], theta_probs=[0.25] * 4,
                 z_atoms=za, z_probs=[1 / len(za)] * len(za), observe_factor=observe_factor)
