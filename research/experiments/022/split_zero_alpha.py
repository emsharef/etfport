"""Experiment 022, Deviation 2: the D12 policy's aim split relative to zero alpha (math's definition), beside the
registered prior-mean split. Reporting only; policies, seeds and beliefs are 022's.

The aim is affine in the belief mean: aim_t = A^lambda_t lambda_hat_t + A^alpha_t alpha_hat_t + a^c_t, with
A = (I - Kx)^-1 Km split by belief block and a^c_t = (I - Kx)^-1 k0 (the fee term). Zero-alpha split: exposure part
A^lambda lambda_hat, alpha part A^alpha alpha_hat (prior mean included), fee term a^c. Registered (M5's text) split:
exposure part = aim with alpha_hat at its prior mean = zero-alpha exposure + fee + A^alpha mu_a 1.
Run: uv run python experiments/022/split_zero_alpha.py   (R = 5,000, the first pass's paths)
"""
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import model  # noqa: E402
import run  # noqa: E402


def beliefs(I, R):
    rngs = [np.random.default_rng([2022, r]) for r in range(R)]
    lam_t, alp_t = run.draw_truth(I, R, rngs)
    Lf = np.linalg.cholesky(I.Sf)
    zf = np.stack([rg.standard_normal((I.T, I.K)) for rg in rngs]) @ Lf.T
    zA = np.stack([rg.standard_normal((I.T, I.N)) for rg in rngs]) * I.sdA
    m = np.tile(I.m0, (R, 1)); ms = []
    for t in range(I.T):
        ms.append(m.copy())
        f = lam_t + zf[:, t]; yA = alp_t + zA[:, t]
        mA = m[:, :I.N] + (yA - m[:, :I.N]) @ I.KA[t].T
        mL = m[:, I.N:] + (f - m[:, I.N:]) @ I.KL[t].T
        m = np.hstack([mA, mL])
    return ms


def main():
    I = model.Inst()
    R = 5000
    ms = beliefs(I, R)
    K = model.riccati(I, np.eye(I.n), I.S, I.Q, I.T)
    n, N, d = I.n, I.N, I.N + I.K
    gross = lambda a, blk: float(np.abs(a[:, blk]).sum(1).mean())  # noqa: E731
    net = lambda a, blk: float(a[:, blk].sum(1).mean())  # noqa: E731
    fb, eb = slice(0, N), slice(N, n)
    print("| t | part | funds gross | ETFs gross | funds net | ETFs net |")
    print("|---|---|---|---|---|---|")
    for t in (0, 20, I.T - 1):
        Kx = np.eye(n) + K[t][:, :n]
        inv = np.linalg.inv(np.eye(n) - Kx)
        Km, k0 = K[t][:, n:n + d], K[t][:, n + d]
        m = ms[t]
        alpha_part = m[:, :N] @ (inv @ Km[:, :N]).T
        expo_zero = m[:, N:] @ (inv @ Km[:, N:]).T
        fee = np.tile(inv @ k0, (R, 1))
        aim = alpha_part + expo_zero + fee
        mX = m.copy(); mX[:, :N] = I.m0[:N]
        expo_prior = mX[:, :N] @ (inv @ Km[:, :N]).T + expo_zero + fee      # registered: alpha at its prior mean
        for lab, a in (("aim", aim), ("exposure part, zero alpha", expo_zero), ("alpha part (prior mean included)", alpha_part),
                       ("fee term", fee), ("exposure part, alpha at prior mean (registered)", expo_prior),
                       ("alpha revision (aim minus registered exposure part)", aim - expo_prior)):
            print(f"| {t} | {lab} | {gross(a, fb):.2f} | {gross(a, eb):.2f} | {net(a, fb):+.2f} | {net(a, eb):+.2f} |")


if __name__ == "__main__":
    main()
