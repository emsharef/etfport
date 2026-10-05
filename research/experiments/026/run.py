"""Experiment 026: claim 100's single-instrument M7 cells (fund alone; ETF alone; K = 1), returns off and on.
Registered design: experiments/026-m7-claim100-cells.md.

Fund alone: market loading 1, residual 2%, alpha uncertain (prior N(-0.19%, 0.35%^2)), premium known 1.84%, factor SD
8.54%. ETF alone: loading 1, residual 0.2%, fee 1 bp, premium uncertain (prior N(1.84%, 0.54%^2)). gamma 5, beta 1,
caps [0, 1], directional rates kappa^+ = kappa^- = kappa.
Filter (M5/M7, fixed means): P_t = 1/(1/p0 + t/s2) with s2 the learning noise (fund: residual variance; ETF: factor
variance); the observation's unexpected part w ~ N(0, P_t + s2) moves the belief by eps = k_t w, k_t = P_t/(P_t + s2),
so Var eps = V_t = P_t - P_{t+1}. Predictive: mu_t = lambda + m_t (fund) or m_t - c^E (ETF); Sigma_t = sf^2 + s_res^2 + P_t.
Returns on: gross return g = 1 + mu_t(m) + w + (the independent shock: factor for the fund, ETF residual for the
ETF), so the belief innovation and the return share w. Returns off: g = 1 (pure learning).
Grid DP on (x, m): x in [0, 1.5] (marked holdings may exceed the cap; post-trade x <= 1), step h; m on 41 points
m_0 +- 4 sd(m_T - m_0); expectation by tensor Gauss-Hermite (20 x 20 nodes; 20 when returns are off) with bilinear
interpolation. Bellman step: experiment 023's exact L1 transform (fastdp.l1).
Run: uv run python experiments/026/run.py   (writes experiments/026/results.json)
"""
import importlib.util
import json
import os
from multiprocessing import Pool
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
_s = importlib.util.spec_from_file_location("fastdp", ROOT / "experiments" / "023" / "fastdp.py")
fastdp = importlib.util.module_from_spec(_s); _s.loader.exec_module(fastdp)

GAMMA, BETA, SF, LAM = 5.0, 1.0, 0.0854, 0.0184
CELLS = {
    "fund": dict(p0=0.0035 ** 2, m0=-0.0019, s2=0.02 ** 2, sres=0.02, other_sd=SF, mu_shift=LAM),
    "etf": dict(p0=0.0054 ** 2, m0=LAM, s2=SF ** 2, sres=0.002, other_sd=0.002, mu_shift=-0.0001),
}
Z, W = np.polynomial.hermite_e.hermegauss(20)
W = W / W.sum()


def moments(c, T):
    P = [1.0 / (1.0 / c["p0"] + t / c["s2"]) for t in range(T + 2)]
    Sig = [SF ** 2 + c["sres"] ** 2 + P[t] for t in range(T + 2)]
    return P, Sig


def interp2(V, xs, mg, xq, mq):
    """Bilinear interpolation of V (on xs x mg) at arrays xq, mq (clamped)."""
    xq = np.clip(xq, xs[0], xs[-1]); mq = np.clip(mq, mg[0], mg[-1])
    hx = xs[1] - xs[0]; hm = mg[1] - mg[0]
    ix = np.minimum(((xq - xs[0]) / hx).astype(int), len(xs) - 2)
    im = np.minimum(((mq - mg[0]) / hm).astype(int), len(mg) - 2)
    tx = (xq - xs[ix]) / hx; tm = (mq - mg[im]) / hm
    return ((1 - tx) * (1 - tm) * V[ix, im] + tx * (1 - tm) * V[ix + 1, im]
            + (1 - tx) * tm * V[ix, im + 1] + tx * tm * V[ix + 1, im + 1])


def solve(inst, T, kappa, returns, h):
    c = CELLS[inst]
    P, Sig = moments(c, T)
    xs = np.round(np.arange(round(1.5 / h) + 1) * h, 12)
    sd_tot = np.sqrt(P[0] - P[T])
    mg = c["m0"] + np.linspace(-4, 4, 41) * sd_tot
    X, M = np.meshgrid(xs, mg, indexing="ij")
    V = np.zeros(X.shape)
    recs = []
    for t in reversed(range(T)):
        mu = M + c["mu_shift"]
        Wt = X * mu - 0.5 * GAMMA * Sig[t] * X ** 2
        if t < T - 1:
            k = P[t] / (P[t] + c["s2"])
            sw = np.sqrt(P[t] + c["s2"])
            ev = np.zeros(X.shape)
            if returns:
                for z1, w1 in zip(Z, W):
                    for z2, w2 in zip(Z, W):
                        wv = sw * z1
                        g = 1 + mu + wv + c["other_sd"] * z2
                        ev += w1 * w2 * interp2(V, xs, mg, X * g, M + k * wv)
            else:
                for z1, w1 in zip(Z, W):
                    ev += w1 * interp2(V, xs, mg, X, M + k * sw * z1)
            Wt = Wt + BETA * ev
        Wt = np.where(X > 1.0 + 1e-12, -1e18, Wt)
        V, A = fastdp.l1(Wt, kappa * h, kappa * h, 0)
        # bands at each belief point with an interior unconstrained target
        static = 2 * kappa / (GAMMA * Sig[t])
        Vt = P[t] - P[t + 1]
        sd_move = np.sqrt(Vt) / (GAMMA * Sig[t + 1])
        for j, mv in enumerate(mg):
            mu_j = mv + c["mu_shift"]
            xstar = mu_j / (GAMMA * Sig[t])
            if not (0 < xstar < 1):
                continue
            drift = mu_j * (1 / (GAMMA * Sig[t + 1]) - 1 / (GAMMA * Sig[t]))
            i0 = int(round(xstar / h))
            stay = A[:, j] == np.arange(len(xs))
            if not stay[i0]:
                continue
            lo = hi = i0
            while lo > 0 and stay[lo - 1]:
                lo -= 1
            while hi < len(xs) - 1 and xs[hi + 1] <= 1.0 and stay[hi + 1]:
                hi += 1
            rec = dict(t=t, j=j, m=float(mv), lo=float(xs[lo]), hi=float(xs[hi]), width=float(xs[hi] - xs[lo]), static=float(static),
                       interior=bool(lo > 0 and xs[hi] < 1.0), xstar=float(xstar), sd_move=float(sd_move), drift=float(drift))
            # claim 100 part 2d, without marking: target moves over the quadrature nodes against the side-weight bound
            if t <= T - 2:
                k = P[t] / (P[t] + c["s2"]); sw = np.sqrt(P[t] + c["s2"])
                moves = (mv + k * sw * Z + c["mu_shift"]) / (GAMMA * Sig[t + 1]) - xstar
                keep = W > 1e-6
                Uw = float(W[keep & (moves > 0)].sum() / W[keep].sum()); Dw = 1 - Uw
                bound_up = (BETA * 2 * kappa * Uw) / (GAMMA * Sig[t]); bound_dn = (BETA * 2 * kappa * Dw) / (GAMMA * Sig[t])
                small = np.where(moves > 0, moves < bound_up, -moves < bound_dn) & keep
                rec.update(U=Uw, n_nodes_below_bound=int(small.sum()), min_move_ratio=float(np.min(np.abs(moves[keep])) / static))
            recs.append(rec)
    return dict(inst=inst, T=T, kappa=kappa, returns=returns, h=h, P=P[:T + 1], Sigma=Sig[:T + 1],
                static_widths=[2 * kappa / (GAMMA * Sig[t]) for t in range(T)], records=recs)


def keys():
    return [(i, T, k, r, h) for i in CELLS for T in (8, 20) for k in (0.0005, 0.002, 0.01) for r in (False, True)
            for h in (1 / 200, 1 / 400)]


def main():
    with Pool(int(os.environ.get("PROCS", "8"))) as pool:
        res = pool.starmap(solve, keys(), chunksize=1)
    (HERE / "results.json").write_text(json.dumps(res))
    print(f"{len(res)} cells")


if __name__ == "__main__":
    main()
