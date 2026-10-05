"""Experiment 021, Deviation 4: the registered D12 comparison (deferred by Deviation 1), run once math's policy exists.

Math's coefficient form (note 2026-09-28-exp021-two-instances; claim 030's recursion), with rho = 1 and m ordered
(lambda, alpha) in math's G = [[B^A, I_N]; [B^E, 0]]:
    D_t = Lambda + gamma Sigma_t + A_{t+1},  A_T = 0,  A_t = Lambda - Lambda D_t^-1 Lambda,
    C_T = 0, C_t = Lambda D_t^-1 (G + C_{t+1}),  c_T = 0, c_t = Lambda D_t^-1 (c_{t+1} - (0, c^E)),
    K_t = D_t^-1 Lambda,  L_t = D_t^-1 (G + C_{t+1}),  l_t = D_t^-1 (c_{t+1} - (0, c^E)).
Compared coefficient by coefficient with the backward recursion of riccati.py (x_t = Kx x_- + Km m + k0, m ordered
(alpha, lambda)), on every Q1-Q3 instance of run.py. Registered agreement: 1e-8 relative.
Run: uv run python experiments/021/compare_math.py
"""
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
import riccati  # noqa: E402
from model import LAMBDA, Inst, cost_vec  # noqa: E402
from run import GAMMAS, Q_SPECS, TS  # noqa: E402


def math_policy(I):
    n, N, K = I.n, I.N, I.K
    Lam = np.diag(cost_vec(I, LAMBDA))
    Gm = np.hstack([I.B, np.vstack([np.eye(N), np.zeros((I.M, N))])])     # columns (lambda, alpha)
    cE = np.concatenate([np.zeros(N), I.cE[N:]])
    A, C, c = np.zeros((n, n)), np.zeros((n, K + N)), np.zeros(n)
    out = [None] * I.T
    for t in reversed(range(I.T)):
        Dt = Lam + I.gamma * I.S(t) + A
        Di = np.linalg.inv(Dt)
        Kt, Lt, lt = Di @ Lam, Di @ (Gm + C), Di @ (c - cE)
        out[t] = (Kt, Lt, lt)
        A, C, c = Lam - Lam @ Di @ Lam, Lam @ Di @ (Gm + C), Lam @ Di @ (c - cE)
    return out


def main():
    worst = 0.0
    print("| instance | gamma | T | max rel. diff K | max rel. diff L | max rel. diff l |")
    print("|---|---|---|---|---|---|")
    for name in Q_SPECS:
        for g in GAMMAS:
            for T in TS:
                I = Inst(name, *Q_SPECS[name], g, T)
                pol, _, _ = riccati.solve(I)
                mp = math_policy(I)
                N, K = I.N, I.K
                perm = list(range(N, N + K)) + list(range(N))                 # (alpha, lambda) -> (lambda, alpha)
                dk = dl = dc = 0.0
                for t in range(T):
                    Kt, Lt, lt = mp[t]
                    Km = pol[t]["Km"][:, perm]
                    rel = lambda a, b: np.abs(a - b).max() / max(np.abs(b).max(), 1e-300)  # noqa: E731
                    dk = max(dk, rel(pol[t]["Kx"], Kt)); dl = max(dl, rel(Km, Lt)); dc = max(dc, rel(pol[t]["k0"], lt))
                worst = max(worst, dk, dl, dc)
                print(f"| {name} | {g:.0f} | {T} | {dk:.1e} | {dl:.1e} | {dc:.1e} |")
    print(f"\nlargest relative difference over all instances, quarters and coefficients: {worst:.1e} "
          f"({'agrees' if worst < 1e-8 else 'DISAGREES'} at the registered 1e-8)")


if __name__ == "__main__":
    main()
