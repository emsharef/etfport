"""Experiment 022 Part 3: stationary long-horizon instance for D13 (experiment 021's P1 with M5's persistent alpha).

One fund (market loading 1, residual 2%), one market ETF (residual 0.2%, fee 1 bp), market premium known (1.84%,
SD 8.54%); proportional costs kappa (common) and caps [0, 1]; gamma 5; T = 120, rho = 1. Alpha is AR(1):
alpha_{t+1} = Phi alpha_t + (1 - Phi) abar + eta, Var eta = (1 - Phi^2) 0.35%^2, abar = -0.19%. The belief starts at
the steady-state predicted variance P, so (with filtered variance P+ = P s2 / (P + s2), s2 = 2%^2) the belief mean
moves as m' = Phi m + (1 - Phi) abar + Phi eps, eps ~ N(0, P - P+), constant over time. The grid DP is experiment
021's (exact separable L1 transform on the holdings grid, 20-point Gauss-Hermite expectation, linear interpolation in
m) with this mean-reverting drift. Bands are read at t = 20, 40, 60 along the line through the frictionless target.
Run: uv run python experiments/022/stationary.py
"""
import importlib.util
import json
import os
import sys
from multiprocessing import Pool
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
_s = importlib.util.spec_from_file_location("g021", ROOT / "experiments" / "021" / "griddp.py")
g021 = importlib.util.module_from_spec(_s); _s.loader.exec_module(g021)

LAM1, SDF, SDA, SDE, FEE, ABAR, ASD, GAMMA, T = 0.0184, 0.0854, 0.02, 0.002, 0.0001, -0.0019, 0.0035, 5.0, 120
READ_T = (20, 40, 60)


def steady(phi):
    q = (1 - phi ** 2) * ASD ** 2
    P = ASD ** 2
    for _ in range(10000):
        Pp = P * SDA ** 2 / (P + SDA ** 2)
        Pn = phi ** 2 * Pp + q
        if abs(Pn - P) < 1e-18:
            break
        P = Pn
    Pp = P * SDA ** 2 / (P + SDA ** 2)
    innov = phi * np.sqrt(P - Pp)
    msd = np.sqrt(phi ** 2 * (P - Pp) / (1 - phi ** 2))        # stationary sd of the belief mean
    return P, Pp, innov, msd


def solve(phi, kappa, h):
    P, Pp, innov, msd = steady(phi)
    xs = np.round(np.arange(round(1 / h) + 1) * h, 12)
    X0, X1 = np.meshgrid(xs, xs, indexing="ij")
    mg = ABAR + np.linspace(-4, 4, 41) * msd
    S = np.array([[SDF ** 2 + SDA ** 2 + P, SDF ** 2], [SDF ** 2, SDF ** 2 + SDE ** 2]])
    quad = -0.5 * GAMMA * (S[0, 0] * X0 ** 2 + 2 * S[0, 1] * X0 * X1 + S[1, 1] * X1 ** 2)
    V = np.zeros(X0.shape + (41,))
    pol = {}
    for t in reversed(range(T)):
        W = np.empty_like(V)
        for j, mv in enumerate(mg):
            lin = X0 * (LAM1 + mv) + X1 * (LAM1 - FEE)
            if t == T - 1:
                ev = 0.0
            else:
                ev = 0.0
                base = phi * mv + (1 - phi) * ABAR
                for z, w in zip(g021.GH_Z, g021.GH_W):
                    mp = np.clip(base + innov * z, mg[0], mg[-1])
                    k = int(min(max(np.searchsorted(mg, mp) - 1, 0), len(mg) - 2))
                    th = (mp - mg[k]) / (mg[k + 1] - mg[k])
                    ev = ev + w * ((1 - th) * V[..., k] + th * V[..., k + 1])
            W[..., j] = lin + quad + ev
        U, A1 = g021.l1_transform(W, kappa * h, 1)
        U, A0 = g021.l1_transform(U, kappa * h, 0)
        V = U
        if t in READ_T:
            pol[t] = g021.compose([(1, A1), (0, A0)], X0.shape + (41,), 2)
    # frictionless target: argmax of the one-quarter objective on the grid (kappa = 0 makes the future irrelevant)
    bands = []
    for t in READ_T:
        y = pol[t]
        for j, mv in enumerate(mg):
            lin = X0 * (LAM1 + mv) + X1 * (LAM1 - FEE)
            tg = np.unravel_index(np.argmax(lin + quad), X0.shape)
            rec = dict(t=t, m=float(mv), m_index=j, target=[float(xs[tg[0]]), float(xs[tg[1]])], edges=[])
            for i in range(2):
                if tg[i] in (0, len(xs) - 1):
                    rec["edges"].append(None); continue
                idx = [tg[0], tg[1], j]
                line = []
                for xi in range(len(xs)):
                    idx[i] = xi
                    line.append(int(y[i][tuple(idx)]) == xi)
                if not line[tg[i]]:
                    rec["edges"].append(None); continue
                lo = hi = tg[i]
                while lo > 0 and line[lo - 1]:
                    lo -= 1
                while hi < len(xs) - 1 and line[hi + 1]:
                    hi += 1
                rec["edges"].append([float(xs[lo]), float(xs[hi]), bool(lo == 0), bool(hi == len(xs) - 1)])
            bands.append(rec)
    return dict(phi=phi, kappa=kappa, h=h, P=P, P_filtered=Pp, innov_sd=float(innov), belief_sd=float(msd), bands=bands)


def main():
    keys = [(phi, k, h) for phi in (0.80, 0.90, 0.95, 0.98) for k in (0.0005, 0.002, 0.01) for h in (1 / 100, 1 / 200)]
    with Pool(int(os.environ.get("PROCS", "8"))) as pool:
        res = pool.starmap(solve, keys)
    (HERE / "stationary.json").write_text(json.dumps(res))
    print(f"{len(res)} configurations")


if __name__ == "__main__":
    main()
