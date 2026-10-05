"""Experiment 023 Part B: claim 029 on a generic M6 target, one instrument, exact on its lattice.

Target x*_t = x0 + k u on a lattice (symmetric law: steps +-1 in units u = s; skewed law: +4 / -1 in units u = 0.75 s,
i.e. +3 s w.p. 0.2 and -0.75 s w.p. 0.8). No learning, no marking (g = 1), beta = 1, c = gamma Sigma with
Sigma = 0.0854^2, gamma = 5. The objective is M6's in its tracking form: maximize -[(c/2)(x - x*)^2 + C(u)] summed.
Holdings grid step h = static / 200 around x0 = 100 static widths (the zero bound never binds). Cap: none, or a fixed
dollar cap at x0 + 0.5 static. The Bellman step is the exact L1 conjugate on the grid (fastdp.l1).
Run: uv run python experiments/023/partB.py   (writes experiments/023/partB.json)
"""
import json
import os
import sys
from multiprocessing import Pool
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fastdp  # noqa: E402

GAMMA, SIG2, BETA = 5.0, 0.0854 ** 2, 1.0
C = GAMMA * SIG2
LAWS = {"symmetric": ([+1, -1], [0.5, 0.5], 1.0), "skewed": ([+4, -1], [0.2, 0.8], 0.75)}   # steps, probs, unit/s
COSTS = {"5/5 bp": (0.0005, 0.0005), "100/0 bp": (0.01, 0.0)}


def solve(law, cost, ratio, T, capped):
    steps, probs, unit_per_s = LAWS[law]
    kp, km = COSTS[cost]
    static = (kp + km) / C
    s = ratio * static
    u = unit_per_s * s
    h = static / 200
    x0 = 100 * static
    kmin, kmax = min(steps) * T, max(steps) * T
    ks = np.arange(kmin, kmax + 1)
    span = np.ceil((max(abs(kmin), abs(kmax)) * u + 3 * static) / h) * h   # a multiple of h, so x0 is on the grid
    G = int(np.ceil(2 * span / h)) + 1
    xs = x0 - span + h * np.arange(G)
    cap = x0 + 0.5 * static if capped else np.inf
    X, KS = np.meshgrid(xs, ks, indexing="ij")
    target = x0 + KS * u
    V = np.zeros(X.shape)
    U_, D_ = sum(p for st, p in zip(steps, probs) if st > 0), sum(p for st, p in zip(steps, probs) if st < 0)
    tau = BETA * (kp * U_ - km * D_) / C
    recs = []
    for t in reversed(range(T)):
        EV = 0.0
        if t < T - 1:
            for st, p in zip(steps, probs):
                sh = np.full_like(V, -np.inf)
                if st > 0:
                    sh[:, :-st] = V[:, st:]
                else:
                    sh[:, -st:] = V[:, :st]
                EV = EV + p * sh
        W = -0.5 * C * (X - target) ** 2 + BETA * EV
        W = np.where(X > cap, -np.inf, W)
        W = np.where(np.isfinite(W), W, -1e18)
        V, A = fastdp.l1(W, kp * h, km * h, 0)
        # reachable lattice states at t: k in [min(steps) t, max(steps) t] with the right parity/arrangement
        reach = set([0])
        for _ in range(t):
            reach = {k + st for k in reach for st in steps}
        for k in sorted(reach):
            col = int(np.where(ks == k)[0][0])
            stay = A[:, col] == np.arange(G)
            xt = x0 + k * u
            i0 = int(np.argmin(np.abs(xs - xt)))
            if xt > cap or not stay[min(i0, G - 1)]:
                # band may not contain the target when capped; find the no-trade run nearest the target
                idx = np.where(stay)[0]
                if len(idx) == 0:
                    continue
                i0 = int(idx[np.argmin(np.abs(idx - i0))])
            lo = hi = i0
            while lo > 0 and stay[lo - 1]:
                lo -= 1
            while hi < G - 1 and stay[hi + 1]:
                hi += 1
            edge_lo, edge_hi = xs[lo], xs[hi]
            interior = (edge_hi < cap - h) and lo > 0 and hi < G - 1
            pred_lo = xt - kp / C + (tau if t < T - 1 else 0.0)
            pred_hi = xt + km / C + (tau if t < T - 1 else 0.0)
            recs.append(dict(t=t, k=int(k), width_ratio=float((edge_hi - edge_lo) / static), interior=bool(interior),
                             lo=float(edge_lo), hi=float(edge_hi), dev_lo_h=float((edge_lo - pred_lo) / h),
                             dev_hi_h=float((edge_hi - pred_hi) / h)))
    min_step = min(abs(st) for st in steps) * u
    coarse = min_step > (1 + BETA) * static          # claim 029 part 1d's sufficient condition (strict)
    boundary = abs(min_step - (1 + BETA) * static) < 1e-12 * static
    return dict(law=law, cost=cost, ratio=ratio, T=T, capped=capped, static=static, h=h, s=s, tau=tau,
                coarse_sufficient=bool(coarse), on_boundary=bool(boundary), records=recs)


def keys():
    return [(law, cost, r, T, cap) for law in LAWS for cost in COSTS for r in (0.25, 0.5, 1, 2, 4)
            for T in (4, 8, 20) for cap in (False, True)]


def main():
    with Pool(int(os.environ.get("PROCS", "8"))) as pool:
        res = pool.starmap(solve, keys(), chunksize=1)
    (HERE / "partB.json").write_text(json.dumps(res))
    print(f"{len(res)} cells")


if __name__ == "__main__":
    main()
