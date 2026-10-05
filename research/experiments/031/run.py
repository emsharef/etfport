"""Experiment 031: claims 036 and 038 B3 (when anticipating learning or mean reversion changes today's target and
trade, M5 separated homogeneous case) against an independent exact solve.
Registered design: experiments/031-anticipation-check.md.  Run: uv run python experiments/031/run.py

Reference: M5's decoupled Kalman filter with persistence (experiment 025's variant: prediction P_{t+1} = Phi P^post Phi'
+ Q, mean E_t m_{t+1} = Phi m_t + (I - Phi) theta_bar), and experiment 028's discounted Riccati recursion over all
instruments on s = (x_-, m, 1), with the mean dynamics in the continuation. Formula side: the claims' definitions,
coded here (no import from checks/).
"""
import itertools
import json
import multiprocessing as mp
import time
from pathlib import Path

import numpy as np
from scipy.optimize import brentq

HERE = Path(__file__).resolve().parent
SIGA, GAMMA = 0.02, 5.0
SIG2 = SIGA ** 2
SF = np.diag([0.08 ** 2, 0.04 ** 2])
LAM0 = np.array([0.015, 0.005])
PL0 = np.diag([0.005 ** 2, 0.005 ** 2])
BA = np.array([[1.0, 0.5], [1.0, 0.2], [1.0, -0.3]])
BE = np.array([[1.0, 0.0], [0.9, 0.4]])
N, K = 3, 2
KAPPAS = [0.01, 0.03, 0.1, 0.23, 0.5, 0.75]
LAMR = [0.01, 0.1, 1.0, 10.0, 100.0]
TS = [2, 4, 8, 20]
RHOS = [0.95, 1.0]
LAMES = [1e-6, 1e-8, 1e-10]
PHIS = [0.0, 0.5, 0.8, 0.95, 1.0]
NAMED = {"equity-style": dict(s2r=0.03, lamA=0.1, T=12), "fixed-income-style": dict(s2r=0.3, lamA=0.5, T=12)}
AHAT = 0.002


# ---------------------------------------------------------------- reference ----------
class Ref:
    def __init__(self, s2, lamA, rho, T, lamE=1e-10, phi=1.0, Qa=0.0, phiL=1.0, QL=None, abar=0.0, freeze_from=None, learnL=True):
        self.n, self.d = N + BE.shape[0], N + K
        self.B = np.vstack([BA, BE]); self.rho, self.T = rho, T
        self.G = np.zeros((self.n, self.d)); self.G[:N, :N] = np.eye(N); self.G[:, N:] = self.B
        self.Lam = np.concatenate([np.full(N, lamA), np.full(BE.shape[0], lamE)])
        self.Phi = np.diag([phi] * N + [phiL] * K)
        self.tbar = np.concatenate([np.full(N, abar), LAM0])
        # filter (prediction variances at each review)
        PA, PL = s2 * np.eye(N), PL0.copy()
        QA = Qa * np.eye(N); QLm = np.zeros((K, K)) if QL is None else QL
        self.PA, self.PL = [], []
        for _ in range(T + 1):
            self.PA.append(PA); self.PL.append(PL)
            PApost = PA - PA @ np.linalg.solve(PA + SIG2 * np.eye(N), PA)      # covariance form (P may be 0)
            PLpost = np.linalg.inv(np.linalg.inv(PL) + np.linalg.inv(SF)) if learnL else PL
            PA = phi ** 2 * PApost + QA
            PL = phiL ** 2 * PLpost + QLm
        Sr = self.B @ SF @ self.B.T + np.diag(np.concatenate([np.full(N, SIG2), np.zeros(BE.shape[0])]))
        P = lambda t: np.block([[self.PA[t], np.zeros((N, K))], [np.zeros((K, N)), self.PL[t]]])
        self.S = [self.G @ P(t) @ self.G.T + Sr for t in range(T)]

    def riccati(self, S_list, Phi=None):
        Phi = self.Phi if Phi is None else Phi
        n, d = self.n, self.d; ns = n + d + 1
        ix, im, i1 = slice(0, n), slice(n, n + d), n + d
        J = np.zeros((ns, n)); J[ix] = np.eye(n)
        F = np.eye(ns); F[im, im] = Phi; F[im, i1] = (np.eye(d) - Phi) @ self.tbar
        Lu = np.diag(self.Lam); M = np.zeros((ns, ns)); Ks = [None] * len(S_list)
        for t in reversed(range(len(S_list))):
            R = np.zeros((ns, ns))
            R[ix, ix] = -0.5 * GAMMA * S_list[t]; R[ix, im] = 0.5 * self.G; R[im, ix] = 0.5 * self.G.T
            A = R + self.rho * F.T @ M @ F
            H = Lu - 2 * J.T @ A @ J
            Kt = np.linalg.solve(H, 2 * J.T @ A)
            V = A + 2 * A @ J @ Kt + Kt.T @ (J.T @ A @ J - 0.5 * Lu) @ Kt
            M = 0.5 * (V + V.T); Ks[t] = Kt
        return Ks

    def coefs(self, Kt):
        """Fund 0's trade u = -g x_0 + h alpha_hat_0 + c (c at x = 0, alpha_hat = 0, prior premium)."""
        s0 = np.concatenate([np.zeros(self.n), np.zeros(N), LAM0, [1.0]])
        return -Kt[0, 0], Kt[0, self.n], float(Kt[0] @ s0)

    def optimal(self):
        return self.riccati(self.S)

    def static(self, t):
        return self.riccati([self.S[t]] * (self.T - t))[0]


# ---------------------------------------------------------------- formula side ----------
def scalar(lamA, p, T, rho):
    """a_{t+1}, d_t, r_t of the scalar fund recursion."""
    a = [0.0] * (T + 1); d = [0.0] * T; r = [0.0] * T
    for t in range(T - 1, -1, -1):
        r[t] = GAMMA * (SIG2 + p[t]); d[t] = lamA + r[t] + rho * a[t + 1]; a[t] = lamA - lamA ** 2 / d[t]
    return a, d, r


def weights(lamA, p, T, rho, t):
    a, d, r = scalar(lamA, p, T, rho)
    w = []
    for s in range(t, T):
        pr = 1.0
        for u in range(t, s):
            pr *= rho * a[u + 1] / (d[u] - lamA)
        w.append(pr * r[s] / (d[s] - lamA))
    return np.array(w), a, d, r


def formula(lamA, p, T, rho, t):
    w, a, d, r = weights(lamA, p, T, rho, t)
    ps = np.array(p[t:T])
    ell = float(np.sum(w * SIG2 / (SIG2 + ps)))
    kap = p[t] / (SIG2 + p[t])
    L = ell * (SIG2 + p[t]) / SIG2
    dur = float(np.sum(w * np.arange(len(w))))
    wt = w * SIG2 / (SIG2 + ps); wt = wt / wt.sum()
    g = a[t] / lamA
    return dict(L=L, kap=kap, dur=dur, ell=ell, wsum=float(w.sum()), w00=float(w[0]), wt=wt.tolist(), g=g)


def g_const(lamA, r, n, rho):
    a = 0.0
    for _ in range(n):
        dd = lamA + r + rho * a; a = lamA - lamA ** 2 / dd
    return a / lamA


def p_path(s2, T, phi=1.0, Qa=0.0):
    p, out = s2, []
    for _ in range(T + 1):
        out.append(p); p = phi ** 2 * p * SIG2 / (p + SIG2) + Qa
    return out


# ---------------------------------------------------------------- checks ----------
def cell12(args):
    kap0, lamr, T, rho, lamE = args
    s2 = kap0 / (1 - kap0) * SIG2; lamA = lamr * GAMMA * SIG2
    I = Ref(s2, lamA, rho, T, lamE=lamE)
    Ko = I.optimal(); p = [I.PA[t][0, 0] for t in range(T + 1)]
    rows = []
    for t in range(T):
        g, h, c = I.coefs(Ko[t]); gS, hS, cS = I.coefs(I.static(t))
        L = (h / g) / (hS / gS)
        f = formula(lamA, p, T, rho, t)
        aimS = (hS * AHAT + cS) / gS; aim = (h * AHAT + c) / g
        trades = []
        for xm in (0.0, 0.5 * aimS, 2 * aimS):
            u, uS = h * AHAT + c - g * xm, hS * AHAT + cS - gS * xm
            ident = (u - uS) - ((g - gS) * (aimS - xm) + g * (aim / aimS - 1) * aimS)
            rt = GAMMA * (SIG2 + p[t])
            gb = g_const(lamA, rt, T - t, rho) - g_const(lamA, GAMMA * SIG2, T - t, rho)
            aimS_f = AHAT / rt
            bound = gb * abs(aimS_f - xm) + f["g"] * f["kap"] / (1 - f["kap"]) * abs(aimS_f)
            trades.append(dict(xm=xm, du=abs(u - uS), ident=ident, bound=bound))
        rows.append(dict(t=t, L=L, fL=f["L"], kap=f["kap"], dur=f["dur"], wsum=f["wsum"], g=g, gS=gS, fg=f["g"],
                         gbound=g_const(lamA, GAMMA * (SIG2 + p[t]), T - t, rho) - g_const(lamA, GAMMA * SIG2, T - t, rho),
                         c_over_h=abs(c) / abs(h * AHAT), trades=trades))
    return dict(kap0=kap0, lamr=lamr, T=T, rho=rho, lamE=lamE, rows=rows)


def cell3(args):
    kap0, lamr, T, rho, phi, qkind, lamE = args
    s2 = kap0 / (1 - kap0) * SIG2; lamA = lamr * GAMMA * SIG2
    Qa = (1 - phi ** 2) * s2 if qkind == "stationary" else 0.0
    I = Ref(s2, lamA, rho, T, lamE=lamE, phi=phi, Qa=Qa)
    Kphi = I.optimal(); K1 = I.riccati(I.S, Phi=np.diag([1.0] * N + [1.0] * K))
    p = [I.PA[t][0, 0] for t in range(T + 1)]
    rows = []
    for t in range(T):
        gp, hp, _ = I.coefs(Kphi[t]); g1, h1, _ = I.coefs(K1[t])
        M = (hp / gp) / (h1 / g1)
        f = formula(lamA, p, T, rho, t)
        wt = np.array(f["wt"]); Mf = float(np.sum(wt * phi ** np.arange(len(wt))))
        lo = wt[0] + (1 - wt[0]) * phi ** (T - 1 - t)
        rows.append(dict(t=t, M=M, Mf=Mf, lo=lo, gdiff=abs(gp - g1)))
    return dict(kap0=kap0, lamr=lamr, T=T, rho=rho, phi=phi, qkind=qkind, lamE=lamE, rows=rows)


def cell4(args):
    kap0, lamr, T, rho, lamE = args
    s2 = kap0 / (1 - kap0) * SIG2; lamA = lamr * GAMMA * SIG2
    out = dict(kap0=kap0, lamr=lamr, T=T, rho=rho, lamE=lamE)
    I = Ref(s2, lamA, rho, T, lamE=lamE); Ko = I.optimal()
    g, h, _ = I.coefs(Ko[0]); gS, hS, _ = I.coefs(I.static(0))
    out["Lm1"] = (h / g) / (hS / gS) - 1
    I3 = Ref(s2, lamA, rho, T, lamE=lamE, phi=0.5, Qa=0.75 * s2)
    Kp = I3.optimal(); K1 = I3.riccati(I3.S, Phi=np.eye(N + K))
    gp, hp, _ = I3.coefs(Kp[0]); g1, h1, _ = I3.coefs(K1[0])
    out["oneMinusM"] = 1 - (hp / gp) / (h1 / g1)
    # ETF exposure trade at t = 0: same current belief, different premium futures
    s = np.concatenate([np.full(I.n, 0.1), np.full(N, AHAT), LAM0 + 0.002, [1.0]])
    etf = lambda R_: (R_.optimal()[0] @ s)[N:]
    base = etf(I)
    per = etf(Ref(s2, lamA, rho, T, lamE=lamE, phiL=0.5, QL=0.75 * PL0))
    frozen = etf(Ref(s2, lamA, rho, T, lamE=lamE, learnL=False))
    out["etf_persist"] = float(np.abs(per - base).max()); out["etf_precision"] = float(np.abs(frozen - base).max())
    out["etf_trade"] = float(np.abs(base).max())
    return out


def named():
    out = {}
    for nm, v in NAMED.items():
        s2 = v["s2r"] * SIG2; T = v["T"]
        I = Ref(s2, v["lamA"], 1.0, T, lamE=1e-10); Ko = I.optimal(); p = [I.PA[t][0, 0] for t in range(T + 1)]
        g, h, _ = I.coefs(Ko[0]); gS, hS, _ = I.coefs(I.static(0))
        f = formula(v["lamA"], p, T, 1.0, 0)
        out[nm] = dict(L=(h / g) / (hS / gS), fL=f["L"], kap=f["kap"], dur=f["dur"], sharper=1 + (f["kap"] / (1 - f["kap"])) ** 2 * f["dur"],
                       first=1 / (1 - f["kap"]), w00=f["w00"])
        # monotonicity of M_0 in phi on 101 points (stationary Q)
        Ms = []
        for phi in np.linspace(0, 1, 101):
            I3 = Ref(s2, v["lamA"], 1.0, T, lamE=1e-10, phi=phi, Qa=(1 - phi ** 2) * s2)
            gp, hp, _ = I3.coefs(I3.optimal()[0]); g1, h1, _ = I3.coefs(I3.riccati(I3.S, Phi=np.eye(N + K))[0])
            Ms.append((hp / gp) / (h1 / g1))
        out[nm]["M_phi"] = Ms
    return out


def L0(kap0, lamr, T=20):
    s2 = kap0 / (1 - kap0) * SIG2; I = Ref(s2, lamr * GAMMA * SIG2, 1.0, T)
    g, h, _ = I.coefs(I.optimal()[0]); gS, hS, _ = I.coefs(I.static(0))
    return (h / g) / (hS / gS)


def level1(args):
    theta, lamr = args
    f = lambda k: L0(k, lamr) - 1 - theta
    kr = brentq(f, 1e-4, 0.95, xtol=1e-8) if f(1e-4) * f(0.95) < 0 else None
    fs = lambda k: (k / (1 - k)) ** 2 * formula(lamr * GAMMA * SIG2, p_path(k / (1 - k) * SIG2, 20), 20, 1.0, 0)["dur"] - theta
    ks = brentq(fs, 1e-4, 0.95, xtol=1e-8) if fs(1e-4) * fs(0.95) < 0 else None
    return dict(theta=theta, lamr=lamr, exact=kr, sharper=ks, first=theta / (1 + theta))


def M0(phi, lamr, T=20, kap0=0.23):
    s2 = kap0 / (1 - kap0) * SIG2
    I = Ref(s2, lamr * GAMMA * SIG2, 1.0, T, phi=phi, Qa=(1 - phi ** 2) * s2)
    gp, hp, _ = I.coefs(I.optimal()[0]); g1, h1, _ = I.coefs(I.riccati(I.S, Phi=np.eye(N + K))[0])
    return (hp / gp) / (h1 / g1), formula(lamr * GAMMA * SIG2, [I.PA[t][0, 0] for t in range(T + 1)], T, 1.0, 0)


def level3(args):
    theta, lamr = args
    f = lambda ph: 1 - M0(ph, lamr)[0] - theta
    pr = brentq(f, 0.0, 1.0, xtol=1e-8) if f(0.0) * f(1.0) < 0 else None
    def fb(ph):
        _, fo = M0(ph, lamr); return (1 - fo["wt"][0]) * (1 - ph ** 19) - theta
    pb = brentq(fb, 0.0, 1.0, xtol=1e-8) if fb(0.0) * fb(1.0) < 0 else None
    return dict(theta=theta, lamr=lamr, exact=pr, bound=pb)


def rounded(o):
    """Floats to 10 significant digits (the checks use about 1e-9 at most)."""
    if isinstance(o, float):
        return float(f"{o:.10g}")
    if isinstance(o, dict):
        return {k: rounded(v) for k, v in o.items()}
    if isinstance(o, (list, tuple)):
        return [rounded(v) for v in o]
    return o


def main():
    t0 = time.time(); S = {}
    with mp.Pool(9) as pool:
        S["c12"] = pool.map(cell12, list(itertools.product(KAPPAS, LAMR, TS, RHOS, LAMES))); print("c12", time.time() - t0, flush=True)
        S["c3"] = pool.map(cell3, list(itertools.product(KAPPAS, LAMR, TS, RHOS, PHIS, ("stationary", "zero"), LAMES))); print("c3", time.time() - t0, flush=True)
        S["c4"] = pool.map(cell4, list(itertools.product(KAPPAS, [1e-4, 1e-3, 1e-2] + LAMR, TS, RHOS, LAMES))); print("c4", time.time() - t0, flush=True)
        lam_grid = [float(v) for v in np.logspace(-2, 2, 13)]
        S["level1"] = pool.map(level1, list(itertools.product([0.01, 0.05, 0.1], lam_grid)))
        S["level3"] = pool.map(level3, list(itertools.product([0.01, 0.05, 0.1], lam_grid))); print("levels", time.time() - t0, flush=True)
    S["named"] = named()
    S["seconds"] = time.time() - t0
    json.dump(rounded(S), open(HERE / "summary.json", "w"), separators=(",", ":"))
    print("done", S["seconds"])


if __name__ == "__main__":
    main()
