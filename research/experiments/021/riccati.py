"""Experiment 021, quadratic costs: exact backward recursion on the quadratic value function.

State s = (x_-, m, 1) with m the belief mean (all components; known ones never move). V_T = 0. At t,
    f(x; s) = x'(H m + g0) - (gamma/2) x' S_t x - (1/2)(x - x_-)' Lambda (x - x_-) + E V_{t+1}(x, m + eps),
eps ~ N(0, diag Q_t), and E[w' M w] = w' M w + tr(M_mm diag Q_t) for w = (x, m, 1). f is a quadratic form in
y = (x, s); maximizing over x gives x* = K s and V_t(s) = s' (F_ss - F_sx F_xx^-1 F_xs) s.
"""
import numpy as np

from model import cost_vec, LAMBDA


def solve(I):
    n, d = I.n, len(I.m0())
    Lam = np.diag(cost_vec(I, LAMBDA))
    H, g0 = I.H(), I.g0()
    ns = n + d + 1                       # s = (x_-, m, 1)
    M = np.zeros((n + d + 1, n + d + 1))  # V_{t+1} as a form in w = (x, m, 1)
    pol, const = [None] * I.T, 0.0
    consts = [0.0] * (I.T + 1)
    for t in reversed(range(I.T)):
        S = I.S(t)
        # y = (x, x_-, m, 1): indices
        ix, iu, im, i1 = slice(0, n), slice(n, 2 * n), slice(2 * n, 2 * n + d), 2 * n + d
        F = np.zeros((2 * n + d + 1, 2 * n + d + 1))
        F[ix, ix] += -0.5 * I.gamma * S - 0.5 * Lam
        F[ix, iu] += 0.5 * Lam; F[iu, ix] += 0.5 * Lam
        F[iu, iu] += -0.5 * Lam
        F[ix, im] += 0.5 * H; F[im, ix] += 0.5 * H.T
        F[ix, i1] += 0.5 * g0; F[i1, ix] += 0.5 * g0
        # continuation: w = (x, m, 1) -> positions (ix, im, i1)
        pos = list(range(0, n)) + list(range(2 * n, 2 * n + d)) + [i1]
        F[np.ix_(pos, pos)] += M
        c = consts[t + 1] + float(np.trace(M[n:n + d, n:n + d] @ I.Q(t)))
        Fxx, Fxs = F[ix, ix], F[ix, n:]
        K = -np.linalg.solve(Fxx, Fxs)              # x* = K s, s = (x_-, m, 1)
        Vs = F[n:, n:] + Fxs.T @ K                   # F_ss - F_sx Fxx^-1 F_xs
        Vs = 0.5 * (Vs + Vs.T)
        resid = np.abs(Fxx @ K + Fxs).max()
        pol[t] = dict(Kx=K[:, :n], Km=K[:, n:n + d], k0=K[:, n + d], resid=float(resid))
        M, consts[t] = Vs, c
    return pol, M, consts[0]


def value(M, c, s):
    return float(s @ M @ s) + c


def aim(I, p, m):
    """x_t = Kx x_- + Km m + k0; aim = (I - Kx)^-1 (Km m + k0); alpha part from the alpha block of m."""
    n = I.n
    A = np.linalg.inv(np.eye(n) - p["Kx"])
    ma = np.concatenate([m[:I.N], np.zeros(len(m) - I.N)])
    full = A @ (p["Km"] @ m + p["k0"])
    alpha_part = A @ (p["Km"] @ ma)
    return full, alpha_part, full - alpha_part
