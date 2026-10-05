"""Experiment 022: data, the calibrated M5 instance, M5's Kalman filter (fixed means), and the time-varying Riccati
recursion with a trade-selection matrix. Registered design: experiments/022-m5-realistic-value.md.
"""
import hashlib
import io
import urllib.request
import zipfile
from pathlib import Path

import numpy as np
import pandas as pd

HERE = Path(__file__).resolve().parent
CACHE = HERE / "cache"
URL = ("https://mba.tuck.dartmouth.edu/pages/faculty/ken.french/Data_Library/Historical_Archives/"
       "08%202025%20Update/ftp/F-F_Research_Data_5_Factors_2x3_CSV.zip")
SHA = "42492fc7fe23de2c44058e77414e1d35c451bf8d289dfff75c5b80c2804324e2"
FACTORS = ["MktRF", "SMB", "HML", "RMW", "CMA"]


def ff5_quarterly():
    """Quarterly FF5 returns 1963Q3-2025Q2 from the pinned archived file (cached, never committed); experiment
    001's compounding: Mkt-RF as (1 + Mkt-RF + RF) products minus (1 + RF) products, long-short factors (1 + x)."""
    f = CACHE / "ff5_2025-07cut.zip"
    if not f.exists():
        CACHE.mkdir(exist_ok=True)
        f.write_bytes(urllib.request.urlopen(urllib.request.Request(URL, headers={"User-Agent": "Mozilla/5.0"}), timeout=60).read())
    raw = f.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == SHA, "pinned file changed"
    text = zipfile.ZipFile(io.BytesIO(raw)).read("F-F_Research_Data_5_Factors_2x3.csv").decode("latin-1")
    rows, started = [], False
    for line in text.splitlines():
        s = line.strip()
        if s.startswith(",Mkt-RF"):
            if started:
                break
            started = True
            continue
        if started:
            p = [x.strip() for x in s.split(",")]
            if len(p) == 7 and len(p[0]) == 6 and p[0].isdigit():
                rows.append([p[0]] + [float(x) / 100 for x in p[1:]])
            elif rows:
                break
    m = pd.DataFrame(rows, columns=["ym", "MktRF", "SMB", "HML", "RMW", "CMA", "RF"])
    m.index = pd.PeriodIndex(pd.to_datetime(m.pop("ym"), format="%Y%m"), freq="M")
    g = m.groupby(m.index.asfreq("Q"))
    q = pd.DataFrame({"MktRF": g.apply(lambda d: (1 + d.MktRF + d.RF).prod() - (1 + d.RF).prod())})
    for c in ["SMB", "HML", "RMW", "CMA"]:
        q[c] = g.apply(lambda d, c=c: (1 + d[c]).prod() - 1)
    q = q[g.size() == 3]
    return q.loc[pd.Period("1963Q3", "Q"):pd.Period("2025Q2", "Q")]


# ---- assumed calibration (registered)
ETF_B = np.array([[1, 0, 0, 0, 0], [1, 0.8, 0.2, 0, 0], [1, 0, 0.6, 0, 0], [1, 0, -0.4, 0, 0],
                  [1, 0, 0, 0.4, 0], [1, 0, 0, 0, 0.4], [1, 0.8, 0.6, 0, 0], [1, 0.3, 0.1, 0, 0]], float)
ETF_FEE = np.array([1, 4, 4, 4, 5, 5, 5, 5]) * 1e-4
ETF_SD = 0.003
N_FUNDS = 30
ALPHA_M, ALPHA_SD, S_BAR = -0.0019, 0.0035, 0.0025 / 4
BSW = (np.array([-0.008, 0.0, 0.0095]), np.array([0.240, 0.754, 0.006]))


class Inst:
    """The calibrated M5 instance (reference case). Order: instruments (funds, then ETFs); theta = (alpha, lambda)."""

    def __init__(self, gamma=5.0, lamA=0.1, lamE=0.01, T=40):
        q = ff5_quarterly()
        self.nq = len(q)
        self.lam_hat = q[FACTORS].mean().to_numpy()
        self.Sf = q[FACTORS].cov().to_numpy()
        rng = np.random.default_rng(2022)
        beta = rng.uniform(0.85, 1.15, N_FUNDS)
        tilts = rng.normal(0, 0.3, (N_FUNDS, 4))
        self.BA = np.column_stack([beta, tilts])
        self.sdA = rng.uniform(0.01, 0.03, N_FUNDS)
        self.BE = ETF_B
        self.N, self.M, self.K = N_FUNDS, len(ETF_B), 5
        self.n = self.N + self.M
        self.B = np.vstack([self.BA, self.BE])
        self.cE = ETF_FEE
        self.DA = self.sdA ** 2
        self.D = np.concatenate([self.DA, np.full(self.M, ETF_SD ** 2)])
        self.Sigma_r = self.B @ self.Sf @ self.B.T + np.diag(self.D)
        self.gamma, self.T = gamma, T
        self.Lam = np.concatenate([np.full(self.N, lamA), np.full(self.M, lamE)])
        # prior (M5 pooled alpha block; premium prior from the sample)
        s2 = ALPHA_SD ** 2 - S_BAR ** 2
        self.P0A = S_BAR ** 2 * np.ones((self.N, self.N)) + s2 * np.eye(self.N)
        self.P0L = self.Sf / self.nq
        self.m0 = np.concatenate([np.full(self.N, ALPHA_M), self.lam_hat])
        self.G = np.hstack([np.vstack([np.eye(self.N), np.zeros((self.M, self.N))]), self.B])   # mu = G m + g0
        self.g0 = np.concatenate([np.zeros(self.N), -self.cE])
        self.x_inc = np.concatenate([np.full(self.N, 0.5 / self.N), [0.5], np.zeros(self.M - 1)])
        self._filter()

    def _filter(self):
        """Deterministic posterior covariances and gains (fixed means): alpha from r^A - B^A f (noise D_A),
        lambda from f (noise Sigma_f); blocks decouple (M5 property (ii))."""
        self.PA, self.PL, self.KA, self.KL = [], [], [], []
        PA, PL = self.P0A.copy(), self.P0L.copy()
        iDA, iSf = np.diag(1 / self.DA), np.linalg.inv(self.Sf)
        for t in range(self.T + 1):
            self.PA.append(PA); self.PL.append(PL)
            PAn = np.linalg.inv(np.linalg.inv(PA) + iDA)
            PLn = np.linalg.inv(np.linalg.inv(PL) + iSf)
            self.KA.append(PAn @ iDA); self.KL.append(PLn @ iSf)      # m' = m + K (obs - m)
            PA, PL = PAn, PLn

    def P(self, t):
        d = self.N + self.K
        P = np.zeros((d, d)); P[:self.N, :self.N] = self.PA[t]; P[self.N:, self.N:] = self.PL[t]
        return P

    def S(self, t):
        return self.G @ self.P(t) @ self.G.T + self.Sigma_r

    def Q(self, t):
        return self.P(t) - self.P(t + 1)


def riccati(I, E, S_of_t, Q_of_t, T):
    """Time-varying recursion. State s = (x_-, m, 1); trade u (columns of E), x = x_- + E u; cost (1/2) u' Lam_u u.
    V_t(s) = max_u [ w'(R_t + M_{t+1}) w - (1/2) u' Lam_u u ] with w = s + J u, J = [E; 0; 0], where w'R_t w is
    x'(G m + g0) - (gamma/2) x' S_t x. Returns per-t K (u* = K s) and the value forms M_t (the constant tr(M Q) terms
    are not needed: values are measured by simulation)."""
    n, d = I.n, I.N + I.K
    ns = n + d + 1
    ix, im, i1 = slice(0, n), slice(n, n + d), n + d
    J = np.zeros((ns, E.shape[1])); J[ix] = E
    Lu = E.T @ np.diag(I.Lam) @ E
    M = np.zeros((ns, ns))
    Ks = [None] * T
    for t in reversed(range(T)):
        R = np.zeros((ns, ns))
        R[ix, ix] = -0.5 * I.gamma * S_of_t(t)
        R[ix, im] = 0.5 * I.G; R[im, ix] = 0.5 * I.G.T
        R[ix, i1] = 0.5 * I.g0; R[i1, ix] = 0.5 * I.g0
        A = R + M
        H = Lu - 2 * J.T @ A @ J
        K = np.linalg.solve(H, 2 * J.T @ A)
        V = A + 2 * A @ J @ K + K.T @ (J.T @ A @ J - 0.5 * Lu) @ K
        M = 0.5 * (V + V.T)
        Ks[t] = K
    return Ks
