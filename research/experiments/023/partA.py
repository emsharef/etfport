"""Experiment 023 Part A: experiment 021's P1 and P2 re-solved for claim 029's checks (bands extracted on the fly).

Model: experiment 021's M5 code (experiments/021/model.py, reused unchanged): proportional costs, caps [0, 1], no
marking, predictive S_t, belief law by 20-point Gauss-Hermite with linear interpolation on 41 belief points. The Bellman
step is the exact L1 conjugate on the holdings grid (fastdp.l1, identical to 021's transform).
Per quarter, belief point and instrument with an interior frictionless (grid) target, the no-trade band is read along
the line through the targets. Reported: width / static width (kappa^+ + kappa^-)/c_t with c_t = gamma S_t,ii; the
target-innovation ratio r_t; the regime class; for P2 at T-1, the fund-1 band centre against the ETF's deviation.
Run: uv run python experiments/023/partA.py   (writes experiments/023/partA.json)
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
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "experiments" / "021"))
import fastdp  # noqa: E402
from model import Inst  # noqa: E402

_s = importlib.util.spec_from_file_location("g021", ROOT / "experiments" / "021" / "griddp.py")
g021 = importlib.util.module_from_spec(_s); _s.loader.exec_module(g021)
SPECS = {"P1": (1, 1, 1, [0], False), "P2": (2, 1, 1, [0], False)}
GAMMA = 5.0


def mgrid(I):
    sd = np.sqrt(I.P(0)[0, 0] - I.P(I.T)[0, 0])
    return I.m0()[0] + np.linspace(-4, 4, 41) * sd


def section_width(S, kap, mu, tgt, i, G, xs):
    """Deviation 2: claim 029 part 2c's static no-trade parallelotope, x* + (gamma S)^-1 prod [-kappa, kappa] with
    one-sided conditions at the bounds, sectioned along instrument i through the others' grid targets. Returns the
    section's width, clipped to [0, 1]."""
    n = len(tgt)
    xstar = np.linalg.solve(GAMMA * S, mu)
    lo, hi = 0.0, 1.0
    for k in range(n):
        # condition on x_i: gamma [S (x - x*)]_k in [-kap_k, kap_k] (interior k), one-sided if k at a bound
        base = GAMMA * sum(S[k, l] * (tgt[l] - xstar[l]) for l in range(n) if l != i) - GAMMA * S[k, i] * xstar[i]
        a = GAMMA * S[k, i]
        at0 = (k != i and tgt[k] <= 0.0)
        at1 = (k != i and tgt[k] >= 1.0)
        lower_ok = not at1          # the >= -kappa condition applies unless x_k sits at its cap
        upper_ok = not at0          # the <= +kappa condition applies unless x_k sits at zero
        if a > 0:
            if lower_ok:
                lo = max(lo, (-kap[k] - base) / a)
            if upper_ok:
                hi = min(hi, (kap[k] - base) / a)
        elif a < 0:
            if lower_ok:
                hi = min(hi, (-kap[k] - base) / a)
            if upper_ok:
                lo = max(lo, (kap[k] - base) / a)
    return float(max(hi - lo, 0.0))


def run_line(stay, i0):
    lo = hi = i0
    while lo > 0 and stay[lo - 1]:
        lo -= 1
    while hi < len(stay) - 1 and stay[hi + 1]:
        hi += 1
    return lo, hi


def solve(name, kf, ke, T, h):
    I = Inst(name, *SPECS[name], GAMMA, T)
    n = I.n
    kap = np.array([kf] * I.N + [ke] * I.M)
    xs = np.round(np.arange(round(1 / h) + 1) * h, 12)
    G = len(xs)
    X = np.meshgrid(*([xs] * n), indexing="ij")
    xf = np.stack([x.ravel() for x in X], 1)
    mg = mgrid(I)
    H = I.H()
    V = np.zeros(X[0].shape + (len(mg),))
    recs, slopes = [], []
    for t in reversed(range(T)):
        S = I.S(t)
        quad = -0.5 * GAMMA * np.einsum("pi,ij,pj->p", xf, S, xf).reshape(X[0].shape)
        q = np.sqrt(I.Q(t)[0, 0])
        W = np.empty_like(V)
        tgt_idx = []
        for j, mv in enumerate(mg):
            m = I.m0().copy(); m[0] = mv
            mu = H @ m + I.g0()
            one = (xf @ mu).reshape(X[0].shape) + quad
            tgt_idx.append(np.unravel_index(np.argmax(one), X[0].shape))
            ev = 0.0
            if t < T - 1:
                for z, w in zip(g021.GH_Z, g021.GH_W):
                    mp = np.clip(mv + q * z, mg[0], mg[-1])
                    k = int(min(max(np.searchsorted(mg, mp) - 1, 0), len(mg) - 2))
                    th = (mp - mg[k]) / (mg[k + 1] - mg[k])
                    ev = ev + w * ((1 - th) * V[..., k] + th * V[..., k + 1])
            W[..., j] = one + ev
        U, args = W, {}
        for ax in reversed(range(n)):
            U, A = fastdp.l1(U, kap[ax] * h, kap[ax] * h, ax)
            args[ax] = A
        V = U

        def y_of(idx):
            """Optimal post-trade grid indices at pre-trade index tuple idx = (x_0..x_{n-1}, j)."""
            cur = list(idx); y = []
            for ax in range(n):
                ya = int(args[ax][tuple(cur)]); y.append(ya); cur[ax] = ya
            return y

        Sn = I.S(t + 1) if t + 1 <= T else S
        Mt, Mn = np.linalg.inv(GAMMA * S), np.linalg.inv(GAMMA * Sn)
        sd_innov = np.abs(Mn @ H[:, 0]) * q                     # stochastic part of x*_{t+1} - x*_t, per instrument
        mu_j = []
        for jj, mv2 in enumerate(mg):
            m2 = I.m0().copy(); m2[0] = mv2
            mu_j.append(H @ m2 + I.g0())
        for j, mv in enumerate(mg):
            tg = tgt_idx[j]
            m = I.m0().copy(); m[0] = mv
            drift = (Mn - Mt) @ (H @ m + I.g0())
            for i in range(n):
                if tg[i] in (0, G - 1):
                    continue
                own = np.zeros(G, bool); allst = np.zeros(G, bool)
                for xi in range(G):
                    idx = list(tg) + [j]; idx[i] = xi
                    y = y_of(tuple(idx))
                    own[xi] = y[i] == xi
                    allst[xi] = all(y[k] == idx[k] for k in range(n))
                c = GAMMA * S[i, i]
                static = 2 * kap[i] / c
                rec = dict(t=t, j=j, inst=i, static=float(static), sd_innov=float(sd_innov[i]), drift=float(drift[i]),
                           c=float(c), kappa=float(kap[i]), section=section_width(S, kap, mu_j[j], [xs[k] for k in tg], i, G, xs))
                for lab, st in (("own", own), ("nt", allst)):       # Deviation 1: own-coordinate band and no-trade-set section
                    if st[tg[i]]:
                        lo, hi = run_line(st, tg[i])
                        rec[lab + "_width"] = float(xs[hi] - xs[lo]); rec[lab + "_interior"] = bool(lo > 0 and hi < G - 1)
                    else:
                        rec[lab + "_width"] = None; rec[lab + "_interior"] = False
                recs.append(rec)
            if name == "P2" and t == T - 1 and tg[0] not in (0, G - 1):
                # part 2c (Deviation 1): centre of the no-trade-set section along fund 1, at each fixed ETF holding,
                # with fund 2 at its target; slope of centre on the ETF holding against -S_1E/S_11
                for xe in range(G):
                    st = np.zeros(G, bool)
                    for xi in range(G):
                        idx = (xi, tg[1], xe, j)
                        y = y_of(idx)
                        st[xi] = all(y[k] == idx[k] for k in range(n))
                    near = np.where(st)[0]
                    if len(near) == 0:
                        continue
                    i0 = int(near[np.argmin(np.abs(near - tg[0]))])
                    lo, hi = run_line(st, i0)
                    if lo > 0 and hi < G - 1:
                        slopes.append((j, float(xs[xe]), float((xs[lo] + xs[hi]) / 2)))
    S_last = I.S(T - 1)
    return dict(inst=name, kappa_fund=kf, kappa_etf=ke, T=T, h=h, records=recs, centre_points=slopes,
                predicted_slope=float(-S_last[0, 2] / S_last[0, 0]) if name == "P2" else None)


def keys():
    out = [("P1", kf, 0.0005, T, h) for kf in (0.0001, 0.0005, 0.002, 0.01) for T in (4, 8, 20) for h in (1 / 200, 1 / 400)]
    out += [("P2", kf, 0.0005, T, h) for kf in (0.0001, 0.0005, 0.002, 0.01) for T in (4, 8, 20) for h in (1 / 20, 1 / 40)]
    return out


def main():
    with Pool(int(os.environ.get("PROCS", "6"))) as pool:
        res = pool.starmap(solve, keys(), chunksize=1)
    (HERE / "partA.json").write_text(json.dumps(res))
    print(f"{len(res)} cells")


if __name__ == "__main__":
    main()
