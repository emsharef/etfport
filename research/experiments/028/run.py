"""Experiment 028: D14/D12's input formulas (claims 030-034) against an independent exact solver.
Registered design: experiments/028-d14-formula-check.md.  Run: uv run python experiments/028/run.py

Reference (uses none of the closed forms): M5's decoupled Kalman filter (experiment 022's filter, Phi = I, Q = 0),
a discounted time-varying Riccati recursion over all instruments (experiment 022's `riccati` with the discount
added), and exact values of any linear policy by propagating the second moments of s = (x_-, m, 1).
Formula side: math's code in checks/030-034 and the formulas as stated in math's note.
Writes experiments/028/summary.json and the figures.
"""
import importlib.util
import itertools
import json
import os
import sys
import time
from pathlib import Path

import numpy as np
from scipy.optimize import brentq

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, ROOT / "checks" / rel / "check.py")
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod


_c30 = _load("check030", "030")
sys.path.insert(0, str(ROOT / "checks" / "030"))
_c31 = _load("check031", "031"); _c32 = _load("check032", "032"); _c34 = _load("check034", "034")

SIGA = 0.02
GAMMA = 5.0
SF = np.diag([0.08 ** 2, 0.04 ** 2])
LAM0 = np.array([0.015, 0.005])
PL0 = np.diag([0.005 ** 2, 0.005 ** 2])
BA_ROW = np.array([1.0, 0.5])
RATIOS = [0.01, 0.03, 0.1, 0.3, 1.0, 3.0]
LAMR = [0.1, 1.0, 10.0, 100.0]           # lambda_A / (gamma sigma_A^2)
RHOS = [0.95, 1.0]
TS = [1, 4, 20]
X0S = [0.0, 0.15]
A0S = [-0.004, 0.002]
CONFIGS = [(1, 0.0), (3, 0.0), (3, 0.5)]  # (N, s_bar^2 / s^2)
CES = [0.0, 0.001]
LAMES = [1e-6, 1e-8, 1e-10]
NAMED = {"equity-style": dict(a0=-0.0019, ratio=0.03, lamr=10.0), "fixed-income-style": dict(a0=0.0020, ratio=0.3, lamr=1.0)}


# ---------------------------------------------------------------- reference (independent) ----------
class Ref:
    """M5 separated homogeneous instance. theta = (alpha (N), lambda (K)); instruments (funds, ETFs)."""

    def __init__(self, N, sbar_share, ratio, lamr, rho, T, cE=0.0, lamE=1e-10, BE=None, sig2_pol=None, Sf_pol=None):
        self.N, self.K = N, 2
        self.BE = np.eye(2) if BE is None else np.atleast_2d(BE)
        self.M = self.BE.shape[0]
        self.n = N + self.M
        self.BA = np.tile(BA_ROW, (N, 1))
        self.B = np.vstack([self.BA, self.BE])
        self.sig2 = SIGA ** 2
        self.s2 = ratio * self.sig2
        self.P0A = sbar_share * self.s2 * np.ones((N, N)) + self.s2 * np.eye(N)
        self.gamma, self.rho, self.T = GAMMA, rho, T
        self.lamA = lamr * GAMMA * self.sig2
        self.Lam = np.concatenate([np.full(N, self.lamA), np.full(self.M, lamE)])
        self.cE = np.full(self.M, cE)
        self.G = np.zeros((self.n, N + 2)); self.G[:N, :N] = np.eye(N); self.G[:, N:] = self.B
        self.g0 = np.concatenate([np.zeros(N), -self.cE])
        self.PA, self.PL = [], []
        PA, PL = self.P0A.copy(), PL0.copy()
        for _ in range(T + 1):
            self.PA.append(PA); self.PL.append(PL)
            PA = np.linalg.inv(np.linalg.inv(PA) + np.eye(N) / self.sig2)
            PL = np.linalg.inv(np.linalg.inv(PL) + np.linalg.inv(SF))
        self.S_true = [self._S(t, self.sig2, SF) for t in range(T)]
        self.S_pol = [self._S(t, self.sig2 if sig2_pol is None else sig2_pol, SF if Sf_pol is None else Sf_pol) for t in range(T)]

    def P(self, t):
        d = self.N + 2; P = np.zeros((d, d)); P[:self.N, :self.N] = self.PA[t]; P[self.N:, self.N:] = self.PL[t]; return P

    def _S(self, t, sig2, Sf):
        Sr = self.B @ Sf @ self.B.T + np.diag(np.concatenate([np.full(self.N, sig2), np.zeros(self.M)]))
        return self.G @ self.P(t) @ self.G.T + Sr

    def m0(self, a0):
        a = np.full(self.N, a0) if np.ndim(a0) == 0 else np.asarray(a0, float)
        return np.concatenate([a, LAM0])

    # discounted Riccati over stages S_list (experiment 022's recursion, with rho)
    def riccati(self, S_list):
        n, d = self.n, self.N + 2; ns = n + d + 1
        ix, im, i1 = slice(0, n), slice(n, n + d), n + d
        J = np.zeros((ns, n)); J[ix] = np.eye(n)
        Lu = np.diag(self.Lam)
        M = np.zeros((ns, ns)); Ks = [None] * len(S_list)
        for t in reversed(range(len(S_list))):
            R = np.zeros((ns, ns))
            R[ix, ix] = -0.5 * self.gamma * S_list[t]
            R[ix, im] = 0.5 * self.G; R[im, ix] = 0.5 * self.G.T
            R[ix, i1] = 0.5 * self.g0; R[i1, ix] = 0.5 * self.g0
            A = R + self.rho * M
            H = Lu - 2 * J.T @ A @ J
            K = np.linalg.solve(H, 2 * J.T @ A)
            V = A + 2 * A @ J @ K + K.T @ (J.T @ A @ J - 0.5 * Lu) @ K
            M = 0.5 * (V + V.T); Ks[t] = K
        return Ks

    def policy(self, kind):
        T = self.T
        if kind == "optimal":
            return self.riccati(self.S_pol)
        if kind == "myopic":
            return [self.riccati([self.S_pol[t]])[0] for t in range(T)]
        if kind == "static":
            return [self.riccati([self.S_pol[t]] * (T - t))[0] for t in range(T)]
        raise ValueError(kind)

    def value(self, Ks, x0, a0):
        """Exact expected objective under the TRUE moments, by second-moment propagation of s = (x_-, m, 1)."""
        n, d = self.n, self.N + 2; ns = n + d + 1
        ix, im, i1 = slice(0, n), slice(n, n + d), n + d
        s = np.concatenate([x0, self.m0(a0), [1.0]]); S2 = np.outer(s, s)
        Lu = np.diag(self.Lam); total = 0.0
        for t in range(self.T):
            K = Ks[t]
            F = np.eye(ns); F[ix, :] += K                       # w = s + J u, J = [I; 0; 0]
            W = np.zeros((ns, ns))
            W[ix, ix] = -0.5 * self.gamma * self.S_true[t]
            W[ix, im] = 0.5 * self.G; W[im, ix] = 0.5 * self.G.T
            W[ix, i1] = 0.5 * self.g0; W[i1, ix] = 0.5 * self.g0
            Wt = F.T @ W @ F - 0.5 * K.T @ Lu @ K
            total += self.rho ** t * np.sum(Wt * S2)
            S2 = F @ S2 @ F.T
            S2[im, im] += self.P(t) - self.P(t + 1)             # innovation covariance of the posterior mean
        return total

    def x0vec(self, x0):
        return np.concatenate([np.full(self.N, x0), np.zeros(self.M)])


# ---------------------------------------------------------------- formula side (math's) ----------
def p_path(s2dir, T):
    return [1.0 / (1.0 / s2dir + t / SIGA ** 2) for t in range(T + 1)]


def directions(N, sbar_share, ratio, x0, a0):
    """Per-direction (prior variance, x0, alpha0, multiplicity) of the homogeneous fund block (claim 032)."""
    s2 = ratio * SIGA ** 2
    if N == 1 or sbar_share == 0.0:
        return [(s2, x0, a0, N)]
    return [(s2 + N * sbar_share * s2, np.sqrt(N) * x0, np.sqrt(N) * a0, 1), (s2, 0.0, 0.0, N - 1)]


def scalar_identity(lamA, rho, T, p, x0, a0, kt, lt):
    """Claim 033's identity in the scalar fund block: (1/2) sum rho^t d_t E[e_t^2] along the alternative path."""
    K, L, D = _c34.scalar_coefs(lamA, GAMMA, SIGA ** 2, p, T, rho)
    mu = np.array([x0, a0]); S = np.outer(mu, mu); loss = 0.0
    for t in range(T):
        dv = np.array([kt[t] - K[t], lt[t] - L[t]])
        loss += rho ** t * 0.5 * D[t] * (dv @ S @ dv)
        F = np.array([[kt[t], lt[t]], [0.0, 1.0]]); S = F @ S @ F.T + np.array([[0, 0], [0, p[t] - p[t + 1]]])
    return loss


def alt_coefs(kind, lamA, rho, T, p):
    r = [GAMMA * (SIGA ** 2 + p[t]) for t in range(T)]
    if kind == "myopic":
        return [lamA / (lamA + r[t]) for t in range(T)], [1.0 / (lamA + r[t]) for t in range(T)]
    kt, lt = [], []
    for t in range(T):
        K, L, _ = _c34.scalar_coefs(lamA, GAMMA, SIGA ** 2, [p[t]] * (T - t + 1), T - t, rho)
        kt.append(K[0]); lt.append(L[0])
    return kt, lt


def gap_formula(kind, N, sbar, ratio, lamr, rho, T, x0, a0, credit):
    lamA = lamr * GAMMA * SIGA ** 2; tot = 0.0
    for s2d, xd, ad, mult in directions(N, sbar, ratio, x0, a0 + credit):
        p = p_path(s2d, T); kt, lt = alt_coefs(kind, lamA, rho, T, p)
        tot += mult * scalar_identity(lamA, rho, T, p, xd, ad, kt, lt)
    return tot


def plugin_C(N, sbar, ratio, lamr, rho, T, x0, a0):
    """Claim 034 part 3(i): loss ~ C (d sigma^2)^2; returned per unit eps^2 (d sigma^2 = eps sigma^2)."""
    lamA = lamr * GAMMA * SIGA ** 2; tot = 0.0
    for s2d, xd, ad, mult in directions(N, sbar, ratio, x0, a0):
        p = p_path(s2d, T)
        Kp, Lp = _c34.scalar_derivs(lamA, GAMMA, SIGA ** 2, p, T, rho)
        K, L, D = _c34.scalar_coefs(lamA, GAMMA, SIGA ** 2, p, T, rho)
        mu = np.array([xd, ad]); S = np.outer(mu, mu); C = 0.0
        for t in range(T):
            dv = np.array([Kp[t], Lp[t]]); C += rho ** t * 0.5 * D[t] * (dv @ S @ dv)
            F = np.array([[K[t], L[t]], [0, 1]]); S = F @ S @ F.T + np.array([[0, 0], [0, p[t] - p[t + 1]]])
        tot += mult * C
    return tot * SIGA ** 4


def myopic_plugin(N, sbar, ratio, rho, T, a0, eps):
    tot = 0.0
    for s2d, xd, ad, mult in directions(N, sbar, ratio, 0.0, a0):
        p = p_path(s2d, T)
        r = [GAMMA * (SIGA ** 2 + p[t]) for t in range(T)]; rt = [GAMMA * (SIGA ** 2 * (1 + eps) + p[t]) for t in range(T)]
        tot += mult * sum(rho ** t * 0.5 * r[t] * (1 / rt[t] - 1 / r[t]) ** 2 * (ad ** 2 + p[0] - p[t]) for t in range(T))
    return tot


def threshold_formula(sdir2, lamr, rho, T, t, x, credit):
    lamA = lamr * GAMMA * SIGA ** 2
    _, ell, _ = _c32.ell_weights(lamA, GAMMA, SIGA ** 2, p_path(sdir2, T), T, t, rho)
    return GAMMA * SIGA ** 2 * x / ell - credit


# ---------------------------------------------------------------- checks ----------
def check_c_and_a_and_plugin():
    rows_c, rows_a, rows_p = [], [], []
    for (N, sb), ratio, lamr, rho, T, cE, lamE in itertools.product(CONFIGS, RATIOS, LAMR, RHOS, TS, CES, LAMES):
        I = Ref(N, sb, ratio, lamr, rho, T, cE=cE, lamE=lamE)
        credit = float(BA_ROW @ np.linalg.solve(np.eye(2), np.full(2, cE)))
        Kopt = I.policy("optimal"); Kmy = I.policy("myopic"); Kst = I.policy("static")
        for x0, a0 in itertools.product(X0S, A0S):
            xv = I.x0vec(x0)
            v_opt = I.value(Kopt, xv, a0)
            g_dyn = v_opt - I.value(Kmy, xv, a0); g_learn = v_opt - I.value(Kst, xv, a0)
            f_dyn = gap_formula("myopic", N, sb, ratio, lamr, rho, T, x0, a0, credit)
            f_learn = gap_formula("static", N, sb, ratio, lamr, rho, T, x0, a0, credit)
            rows_c.append(dict(N=N, sb=sb, ratio=ratio, lamr=lamr, rho=rho, T=T, cE=cE, lamE=lamE, x0=x0, a0=a0,
                               v_opt=v_opt, g_dyn=g_dyn, f_dyn=f_dyn, g_learn=g_learn, f_learn=f_learn))
        # (a) thresholds at t in {0, T-1}, given x_{t-1}
        common = sb > 0
        sdir2 = ratio * SIGA ** 2 * (1 + N * sb) if common else ratio * SIGA ** 2
        for t in sorted({0, T - 1}):
            for x in X0S:
                def trade(a):
                    avec = np.full(N, a) if common else np.concatenate([[a], np.zeros(N - 1)])
                    s = np.concatenate([I.x0vec(x), avec, LAM0, [1.0]])
                    return (Kopt[t] @ s)[0]
                root = brentq(trade, -0.2, 0.2, xtol=1e-14, rtol=1e-14, maxiter=500)
                rows_a.append(dict(N=N, sb=sb, ratio=ratio, lamr=lamr, rho=rho, T=T, cE=cE, lamE=lamE, t=t, x=x,
                                   ref=root, formula=threshold_formula(sdir2, lamr, rho, T, t, x, credit)))
        # plug-in residual variance (c^E = 0 only)
        if cE == 0.0:
            for eps in (-0.2, -0.05, -0.01, 0.01, 0.05, 0.2):
                Ip = Ref(N, sb, ratio, lamr, rho, T, lamE=lamE, sig2_pol=SIGA ** 2 * (1 + eps))
                Kp = Ip.policy("optimal")
                for x0, a0 in itertools.product(X0S, A0S):
                    xv = I.x0vec(x0)
                    loss = I.value(Kopt, xv, a0) - I.value(Kp, xv, a0)
                    rows_p.append(dict(N=N, sb=sb, ratio=ratio, lamr=lamr, rho=rho, T=T, lamE=lamE, x0=x0, a0=a0, eps=eps,
                                       loss=loss, Ceps2=plugin_C(N, sb, ratio, lamr, rho, T, x0, a0) * eps ** 2))
    return rows_c, rows_a, rows_p


def plugin_limits():
    out = []
    for (N, sb), ratio, rho, T, lamE in itertools.product(CONFIGS, RATIOS, RHOS, [4, 20], [1e-8, 1e-10]):
        for a0 in A0S:
            for lamr in (1e-4, 1e2, 1e3, 1e4):
                I = Ref(N, sb, ratio, lamr, rho, T, lamE=lamE)
                K0 = I.policy("optimal")
                eps = 0.01
                Ip = Ref(N, sb, ratio, lamr, rho, T, lamE=lamE, sig2_pol=SIGA ** 2 * (1 + eps))
                loss = I.value(K0, I.x0vec(0.15), a0) - I.value(Ip.policy("optimal"), I.x0vec(0.15), a0)
                row = dict(N=N, sb=sb, ratio=ratio, rho=rho, T=T, lamE=lamE, a0=a0, lamr=lamr, eps=eps, loss=loss,
                           Ceps2=plugin_C(N, sb, ratio, lamr, rho, T, 0.15, a0) * eps ** 2, lamA=I.lamA)
                if lamr == 1e-4:
                    row["myopic"] = myopic_plugin(N, sb, ratio, rho, T, a0, eps)
                out.append(row)
    return out


def math_inst(N, sb, ratio, lamr, rho, T, BE):
    """An instance dict in checks/030's conventions (theta = (lambda, alpha)) for checks/031's formula code."""
    K = 2; BE = np.atleast_2d(BE); M = BE.shape[0]
    BA = np.tile(BA_ROW, (N, 1)); B = np.vstack([BA, BE]); s2 = ratio * SIGA ** 2
    SigA = SIGA ** 2 * np.eye(N); SigE = np.zeros((M, M))
    Sig_z = np.block([[SF, np.zeros((K, N)), np.zeros((K, M))], [np.zeros((N, K)), SigA, np.zeros((N, M))],
                      [np.zeros((M, K)), np.zeros((M, N)), SigE]])
    Lz = np.block([[np.eye(K), np.zeros((K, N)), np.zeros((K, M))], [BA, np.eye(N), np.zeros((N, M))], [BE, np.zeros((M, N)), np.eye(M)]])
    H = np.block([[np.eye(K), np.zeros((K, N))], [BA, np.eye(N)], [BE, np.zeros((M, N))]])
    P0 = np.block([[PL0, np.zeros((K, N))], [np.zeros((N, K)), sb * s2 * np.ones((N, N)) + s2 * np.eye(N)]])
    return dict(N=N, M=M, K=K, BA=BA, BE=BE, B=B, Sig_f=SF, Sig_A=SigA, Sig_E=SigE, Sig_z=Sig_z, Sig_y=Lz @ Sig_z @ Lz.T,
                Lz=Lz, H=H, P0=P0, T=T, rho=rho, gamma=GAMMA, Lam=np.diag([lamr * GAMMA * SIGA ** 2] * N + [0.0] * M))


def etf_at(phi_deg):
    """Deviation 2: the single ETF's loading at angle phi from the fund loading (phi = 0: spanned)."""
    b = BA_ROW / np.linalg.norm(BA_ROW); c, s = np.cos(np.radians(phi_deg)), np.sin(np.radians(phi_deg))
    return np.array([[c * b[0] - s * b[1], s * b[0] + c * b[1]]])


def check_d():
    rows = []
    menus = [("two-ETF spanning", np.eye(2))] + [(f"phi={p}", etf_at(p)) for p in (0, 15, 45, 90)]
    for (N, sb), ratio, lamr, rho, T, lamE in itertools.product(CONFIGS, RATIOS, LAMR, RHOS, [4, 20], LAMES):
        for name, BE in menus:
            I = Ref(N, sb, ratio, lamr, rho, T, lamE=lamE, BE=BE)
            K0 = I.policy("optimal")[0]
            ref = np.zeros((N, 2)); h = 1e-6
            for k in range(2):
                e = np.zeros(I.N + 2 + I.n + 1)
                def x_of(dl):
                    s = np.concatenate([I.x0vec(0.1), np.full(N, 0.001), LAM0 + dl, [1.0]])
                    return (s[:I.n] + K0 @ s)[:N]
                dl = np.zeros(2); dl[k] = h
                ref[:, k] = (x_of(dl) - x_of(-dl)) / (2 * h)
            MI = math_inst(N, sb, ratio, lamr, rho, T, BE)
            Ps, _ = _c30.kalman_path(MI)
            red = _c31.reduced(MI, Ps)
            form = _c31.fund_recursion(MI, red)[0]["L"][:, :2]
            PiR, PiU, _ = _c31.projections(MI["BE"])
            rows.append(dict(N=N, sb=sb, ratio=ratio, lamr=lamr, rho=rho, T=T, lamE=lamE, menu=name,
                             unspanned=float(np.linalg.norm(PiU @ BA_ROW)), ref_max=float(np.abs(ref).max()),
                             form_max=float(np.abs(form).max()), diff=float(np.abs(ref - form).max())))
    return rows


def check_factor_cov():
    rows = []
    for (N, sb), ratio, lamr, rho, T, lamE, eps in itertools.product(CONFIGS, RATIOS, LAMR, RHOS, [4, 20], LAMES, [0.05, 0.2]):
        for name, BE in (("two-ETF spanning", np.eye(2)), ("phi=45", etf_at(45))):
            I = Ref(N, sb, ratio, lamr, rho, T, lamE=lamE, BE=BE)
            Ie = Ref(N, sb, ratio, lamr, rho, T, lamE=lamE, BE=BE, Sf_pol=SF * (1 + eps))
            K1, K2 = I.policy("optimal"), Ie.policy("optimal")
            ch = max(np.abs(K1[t][:N] - K2[t][:N]).max() for t in range(T))
            rows.append(dict(N=N, sb=sb, ratio=ratio, lamr=lamr, rho=rho, T=T, lamE=lamE, eps=eps, menu=name, change=float(ch)))
    return rows


def level_sets():
    """Figure 2 data: formula gap per quarter on a fine grid (T = 20, rho = 1, N = 1, x0 = 0, c^E = 0), and the
    reference's 1 bp-per-quarter crossings in the signal-to-noise ratio at fixed lambda ratios."""
    T, rho = 20, 1.0; qsum = T
    rg = np.logspace(-2, np.log10(3), 40); lg = np.logspace(-1, 2, 40)
    out = {}
    for pname, pt in NAMED.items():
        grid = {k: [[gap_formula(k, 1, 0.0, r, l, rho, T, 0.0, pt["a0"], 0.0) / qsum for r in rg] for l in lg] for k in ("myopic", "static")}
        cross = {}
        for k in ("myopic", "static"):
            pts = []
            for l in [0.1, 0.3, 1.0, 3.0, 10.0, 30.0, 100.0]:
                def f(logr):
                    I = Ref(1, 0.0, 10 ** logr, l, rho, T, lamE=1e-10)
                    xv = I.x0vec(0.0)
                    return (I.value(I.policy("optimal"), xv, pt["a0"]) - I.value(I.policy(k), xv, pt["a0"])) / qsum - 1e-4
                lo, hi = -2.0, np.log10(3.0)
                if f(lo) * f(hi) < 0:
                    pts.append([l, 10 ** brentq(f, lo, hi, xtol=1e-6)])
            cross[k] = pts
        out[pname] = dict(ratio_grid=rg.tolist(), lamr_grid=lg.tolist(), grid=grid, cross=cross)
    return out


def monte_carlo(paths=20000):
    out = {}
    for pname, pt in NAMED.items():
        N, T, rho = 3, 20, 1.0
        I = Ref(N, 0.0, pt["ratio"], pt["lamr"], rho, T, lamE=1e-10)
        pols = {k: I.policy(k) for k in ("optimal", "myopic", "static")}
        rng = np.random.default_rng([2028, 0])
        xv = I.x0vec(0.0); m0 = I.m0(pt["a0"])
        th_alpha = m0[:N] + rng.standard_normal((paths, N)) @ np.linalg.cholesky(I.P0A).T
        th_lam = LAM0 + rng.standard_normal((paths, 2)) @ np.linalg.cholesky(PL0).T
        cf = np.linalg.cholesky(SF)
        zf = rng.standard_normal((T, paths, 2)); za = rng.standard_normal((T, paths, N))
        res = {}
        for k, Ks in pols.items():
            m = np.tile(m0, (paths, 1)); x = np.tile(xv, (paths, 1)); val = np.zeros(paths)
            for t in range(T):
                s = np.hstack([x, m, np.ones((paths, 1))])
                u = s @ Ks[t].T; xn = x + u
                mu = m @ I.G.T + I.g0
                val += rho ** t * (np.sum(xn * mu, 1) - 0.5 * GAMMA * np.einsum("pi,ij,pj->p", xn, I.S_true[t], xn)
                                   - 0.5 * np.sum(u * u * I.Lam, 1))
                f = th_lam + zf[t] @ cf.T; ya = th_alpha + SIGA * za[t]
                KA = I.PA[t + 1] / SIGA ** 2; KL = I.PL[t + 1] @ np.linalg.inv(SF)
                m = np.hstack([m[:, :N] + (ya - m[:, :N]) @ KA.T, m[:, N:] + (f - m[:, N:]) @ KL.T])
                x = xn
            res[k] = val
        ex = {k: I.value(Ks, xv, pt["a0"]) for k, Ks in pols.items()}
        out[pname] = {k: dict(exact=ex[k], mc=float(res[k].mean()), se=float(res[k].std(ddof=1) / np.sqrt(paths))) for k in pols}
        for k in ("myopic", "static"):
            d = res["optimal"] - res[k]
            out[pname][f"gap_{k}"] = dict(exact=ex["optimal"] - ex[k], mc=float(d.mean()), se=float(d.std(ddof=1) / np.sqrt(paths)))
    return out


def figures(S):
    import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    fig, axes = plt.subplots(1, 2, figsize=(10, 4))
    for ax, (pname, pt) in zip(axes, NAMED.items()):
        xs = np.linspace(0, 0.3, 31)
        for ratio in RATIOS:
            f = [threshold_formula(ratio * SIGA ** 2, pt["lamr"], 1.0, 20, 0, x, 0.0) * 100 for x in xs]
            ax.plot(xs, f, lw=1, label=f"s^2/sigma^2 = {ratio}")
            I = Ref(1, 0.0, ratio, pt["lamr"], 1.0, 20, lamE=1e-10); K0 = I.policy("optimal")[0]
            pts = []
            for x in xs[::5]:
                pts.append(brentq(lambda a: (K0 @ np.concatenate([I.x0vec(x), [a], LAM0, [1.0]]))[0], -0.2, 0.2, xtol=1e-14) * 100)
            ax.plot(xs[::5], pts, "k.", ms=4)
        ax.set_title(f"{pname}: buy threshold at t = 0 (T = 20)"); ax.set_xlabel("x_{t-1} (fund holding)"); ax.set_ylabel("alpha_hat threshold, % per quarter")
    axes[0].legend(fontsize=7)
    fig.tight_layout(); fig.savefig(HERE / "fig_threshold.png", dpi=130); plt.close(fig)
    fig, axes = plt.subplots(1, 2, figsize=(10, 4))
    for ax, (pname, L) in zip(axes, S["level_sets"].items()):
        R, Lg = np.meshgrid(L["ratio_grid"], L["lamr_grid"])
        for k, col in (("myopic", "C0"), ("static", "C3")):
            ax.contour(R, Lg, np.array(L["grid"][k]), levels=[1e-4], colors=col)
            if L["cross"][k]:
                c = np.array(L["cross"][k]); ax.plot(c[:, 1], c[:, 0], "o", color=col, mfc="none", label=f"{k}: reference crossing")
        ax.set_xscale("log"); ax.set_yscale("log"); ax.set_xlabel("s^2/sigma_A^2"); ax.set_ylabel("lambda_A/(gamma sigma_A^2)")
        ax.set_title(f"{pname}: 1 bp/quarter level sets (T = 20)"); ax.legend(fontsize=7)
    fig.tight_layout(); fig.savefig(HERE / "fig_levelsets.png", dpi=130); plt.close(fig)


def _r(v):
    return float(f"{v:.12g}") if isinstance(v, float) else v


def compact(S):
    """Row lists become column lists; floats keep 12 significant digits (the checks need about 1e-12 relative)."""
    out = {}
    for k, v in S.items():
        if isinstance(v, list) and v and isinstance(v[0], dict):
            out[k] = {c: [_r(r.get(c)) for r in v] for c in dict.fromkeys(c for r in v for c in r)}
        else:
            out[k] = v
    return out


def main():
    t0 = time.time(); S = {}
    S["c"], S["a"], S["plugin"] = check_c_and_a_and_plugin(); print("c/a/plugin", time.time() - t0, flush=True)
    S["plugin_limits"] = plugin_limits(); print("limits", time.time() - t0, flush=True)
    S["d"] = check_d(); print("d", time.time() - t0, flush=True)
    S["factor_cov"] = check_factor_cov(); print("factor", time.time() - t0, flush=True)
    S["level_sets"] = level_sets(); print("levels", time.time() - t0, flush=True)
    S["mc"] = monte_carlo(); print("mc", time.time() - t0, flush=True)
    S["seconds"] = time.time() - t0
    json.dump(compact(S), open(HERE / "summary.json", "w"), separators=(",", ":"))
    figures(S)
    print("done", time.time() - t0)


if __name__ == "__main__":
    main()
