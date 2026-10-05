"""Experiment 021: the D12/D13 fund-of-funds model as registered (ROADMAP reading), and its instances.

Instruments i = 1..n (N funds, then M ETFs), loadings B (n x K). Quarterly returns r = B f + a + e with public
factor returns f = lambda + u, u ~ N(0, Sigma_f) (Sigma_f diagonal), a = (alpha, -c^E), e ~ N(0, D) (diagonal).
theta = (alpha, lambda) has independent Gaussian prior components. Because f is public, alpha is learned from
r - B f = a + e and lambda from f, component by component, so the posterior variances are deterministic:
    P_t(alpha_i) = 1 / (1/p0 + t / d_i),   P_t(lambda_k) = 1 / (1/p0 + t / s_k)
(a zero prior variance means known). The mean m_t is a Gaussian martingale with innovation variance
Q_t = P_t - P_{t+1}, component by component. Predictive moments of r_{t+1}:
    mu_t = B m^lambda_t + (m^alpha_t, -c^E),   S_t = B (Sigma_f + diag P^lambda_t) B' + D + diag(P^alpha_t, 0).
Objective: maximize E sum_{t=0}^{T-1} [ x_t' mu_t - (gamma/2) x_t' S_t x_t - C(x_t - x_{t-1}) ].
"""
from dataclasses import dataclass, field

import numpy as np

# data (French, 1963Q3-2025Q2, per quarter, gross)
LAM = np.array([0.0184, 0.00897])
SDF = np.array([0.0854, 0.06095])
SE_LAM = SDF / np.sqrt(248)                    # 0.54%, 0.39%: sample-mean standard errors
# assumed
ALPHA_M, ALPHA_SD = -0.0019, 0.0035           # Barras-Scaillet-Wermers-matched pooled Gaussian prior, per quarter
# Deviation 3 (M5's pooled prior): alpha_i = a_bar + eta_i, Var(a_bar) = S_BAR^2 (uncertainty about the fund
# population's mean alpha, assumed 0.25% per year), Var(eta_i) = ALPHA_SD^2 - S_BAR^2, so each fund's prior variance
# is unchanged and the alpha block is S_BAR^2 11' + s^2 I.
S_BAR = 0.0025 / 4
FUND_B = [np.array([1.0, 0.3]), np.array([1.0, 0.0]), np.array([0.9, 0.5])]
ETF_B = [np.array([1.0, 0.0]), np.array([0.0, 1.0])]
SD_FUND, SD_ETF, FEE_ETF = 0.02, 0.002, 0.0001


@dataclass
class Inst:
    name: str
    N: int
    M: int
    K: int
    alpha_unc: list          # which funds' alphas are uncertain
    lam_unc: bool
    gamma: float
    T: int
    B: np.ndarray = field(init=False)
    D: np.ndarray = field(init=False)

    def __post_init__(self):
        rows = [FUND_B[i][:self.K] for i in range(self.N)] + [ETF_B[j][:self.K] for j in range(self.M)]
        self.B = np.array(rows)
        self.D = np.array([SD_FUND ** 2] * self.N + [SD_ETF ** 2] * self.M)
        self.cE = np.array([0.0] * self.N + [FEE_ETF] * self.M)

    @property
    def n(self):
        return self.N + self.M

    def P0(self):
        """Prior covariance of theta = (alpha_1..N, lambda_1..K): M5's pooled alpha block over the uncertain funds."""
        d = self.N + self.K
        P = np.zeros((d, d))
        U = list(self.alpha_unc)
        s2 = ALPHA_SD ** 2 - S_BAR ** 2
        for i in U:
            for j in U:
                P[i, j] = S_BAR ** 2 + (s2 if i == j else 0.0)
        if self.lam_unc:
            for k in range(self.K):
                P[self.N + k, self.N + k] = SE_LAM[k] ** 2
        return P

    def p0(self):
        return np.diag(self.P0())

    def obs_var(self):
        return np.concatenate([self.D[:self.N], SDF[:self.K] ** 2])

    def P(self, t):
        """Posterior covariance after t quarters (matrix Kalman update on the uncertain block; fixed means)."""
        P0 = self.P0()
        idx = [i for i in range(len(P0)) if P0[i, i] > 0]
        P = np.zeros_like(P0)
        if idx:
            sub = P0[np.ix_(idx, idx)]
            prec = np.linalg.inv(sub) + t * np.diag(1.0 / self.obs_var()[idx])
            P[np.ix_(idx, idx)] = np.linalg.inv(prec)
        return P

    def Q(self, t):
        """Innovation covariance of the belief mean, P_t - P_{t+1} (matrix)."""
        return self.P(t) - self.P(t + 1)

    def m0(self):
        return np.concatenate([np.full(self.N, ALPHA_M), LAM[:self.K]])

    def H(self):
        """mu = H m + g0."""
        EA = np.zeros((self.n, self.N)); EA[:self.N, :self.N] = np.eye(self.N)
        return np.hstack([EA, self.B])

    def g0(self):
        return -self.cE

    def S(self, t):
        """M5's predictive covariance G P_t G' + Sigma_r, G = [[I_N 0]; [0 0]] (alpha) and B (lambda) columns."""
        P = self.P(t)
        G = self.H()
        return G @ P @ G.T + self.B @ np.diag(SDF[:self.K] ** 2) @ self.B.T + np.diag(self.D)

def instances():
    out = []
    for g in (2.0, 5.0, 10.0):
        for T in (4, 8):
            out += [Inst("Q1", 1, 1, 1, [0], False, g, T), Inst("Q2", 2, 1, 1, [0, 1], True, g, T),
                    Inst("Q3", 3, 2, 2, [0, 1, 2], True, g, T),
                    Inst("P1", 1, 1, 1, [0], False, g, T), Inst("P2", 2, 1, 1, [0], False, g, T)]
    return out


LAMBDA = {"fund": 0.1, "etf": 0.01}          # quadratic cost coefficients
KAPPA = {"fund": 0.01, "etf": 0.0005}        # proportional: 100 bp (EDGAR median deferred charge), 5 bp


def cost_vec(I, table):
    return np.array([table["fund"]] * I.N + [table["etf"]] * I.M)
