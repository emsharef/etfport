"""Experiment 036: claim 107 (the fund's dynamic band with one ETF) against an exact two-instrument dynamic program.
Registered design: experiments/036-d15c-dynamic-band-check.md.  Run: uv run python experiments/036/run.py

M7 tracking form, finite-law variant, fixed Sigma, beta = 1, no marking, no binding bounds. Because Sigma is fixed and
nothing binds, the value depends only on the deviation d = x - x*_t: V_t(d) = max_y [W_t(y) - C(y - d)] with
W_t(y) = -(gamma/2) y' Sigma y + beta E V_{t+1}(y - Delta), Delta the targets' step. The trade cost is separable, so
the exact L1 transform (experiment 023's fastdp.l1) is applied along the ETF axis, then the fund axis. The T = 8 run's
review 8 - k is the first review of the k-review problem (stationarity), so it covers T in {1, 4, 8}.
"""
import itertools
import json
import multiprocessing as mp
import sys
import time
from pathlib import Path

import cvxpy as cp
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "023"))
import fastdp  # noqa: E402

GAMMA, BETA, T = 5.0, 1.0, 8
SEE = 0.0854 ** 2
SAA = 0.0854 ** 2 + 0.02 ** 2
CAP = 1500                                    # Deviation 2: at most this many grid points per axis


def setup(corr, kA, kE):
    SAE = corr * np.sqrt(SAA * SEE)
    S = np.array([[SAA, SAE], [SAE, SEE]])
    cres = GAMMA * (SAA - SAE ** 2 / SEE); rho = SAE / SEE
    return S, cres, rho


def extent(S, kA, kE):
    Mi = np.linalg.inv(GAMMA * S)
    lo = np.array([-(kA[0] + BETA * kA[1]), -(kE[0] + BETA * kE[1])]); hi = np.array([kA[1] + BETA * kA[0], kE[1] + BETA * kE[0]])
    V = np.array([Mi @ np.array([a, e]) for a in (lo[0], hi[0]) for e in (lo[1], hi[1])])
    return V.min(0), V.max(0)


def run_cell(args):
    corr, kA, kE, r, step, hfac = args          # kA, kE: (kappa^+, kappa^-)
    S, cres, rho = setup(corr, kA, kE)
    vmin, vmax = extent(S, kA, kE)
    span = (vmax - vmin) * 1.2
    wA = (kA[0] + kA[1]) / cres
    wE = (kE[0] + kE[1]) / (GAMMA * SEE) if kE[0] + kE[1] > 0 else 2 * 0.001 / (GAMMA * SEE)
    uA, uE = step * wA, step * wE
    hA = max(wA / 100, 1.4 * span[0] / CAP) / hfac; hE = max(wE / 100, 1.4 * span[1] / CAP) / hfac
    sA, sE = max(1, round(uA / hA)), max(1, round(uE / hE))           # lattice steps in grid units
    mA = int(np.ceil((max(-vmin[0], vmax[0]) * 1.2 + 3 * sA * hA) / hA)); mE = int(np.ceil((max(-vmin[1], vmax[1]) * 1.2 + 3 * sE * hE) / hE))
    dA = np.arange(-mA, mA + 1) * hA; dE = np.arange(-mE, mE + 1) * hE
    YA, YE = np.meshgrid(dA, dE, indexing="ij")
    quad = -0.5 * GAMMA * (S[0, 0] * YA ** 2 + 2 * S[0, 1] * YA * YE + S[1, 1] * YE ** 2)
    law = [((+1, +1), (1 + r) / 4), ((-1, -1), (1 + r) / 4), ((+1, -1), (1 - r) / 4), ((-1, +1), (1 - r) / 4)]
    V = np.zeros_like(quad); out = []
    # reduced one-instrument DP (part 3), same fund grid and marginal law
    V1 = np.zeros(len(dA))
    for t in range(T - 1, -1, -1):
        cont = np.zeros_like(V)
        if t < T - 1:
            P = np.pad(V, ((sA, sA), (sE, sE)), mode="edge")
            for (a, e), pr in law:          # E V(y - Delta): index shift by (-a sA, -e sE)
                cont += pr * P[sA - a * sA: sA - a * sA + len(dA), sE - e * sE: sE - e * sE + len(dE)]
        W = quad + BETA * cont
        Z, AE = fastdp.l1(W, kE[0] * hE, kE[1] * hE, axis=1)
        U, AA = fastdp.l1(Z, kA[0] * hA, kA[1] * hA, axis=0)
        V = U
        c1 = np.zeros(len(dA))
        if t < T - 1:
            P1 = np.pad(V1, (sA, sA), mode="edge")
            c1 = 0.5 * (P1[0:len(dA)] + P1[2 * sA:2 * sA + len(dA)])
        U1, A1 = fastdp.l1(-0.5 * cres * dA ** 2 + BETA * c1, kA[0] * hA, kA[1] * hA, axis=0)
        V1 = U1
        out.append(measure(t, dA, dE, AA, AE, A1, S, cres, rho, kA, kE, hA, hE, mA, mE, sA, sE))
    return dict(corr=corr, kA=list(kA), kE=list(kE), r=r, step=step, hfac=hfac, hA=hA, hE=hE, cres=cres, rho=rho, wA=wA,
                sA=sA, sE=sE, rows=out[::-1])


def measure(t, dA, dE, AA, AE, A1, S, cres, rho, kA, kE, hA, hE, mA, mE, sA, sE):
    last = t == T - 1
    b = 0.0 if last else BETA
    rp, rm = max(rho, 0), max(-rho, 0)
    Hp = rp * (kE[0] + b * kE[1]) + rm * (kE[1] + b * kE[0]); Hm = rp * (kE[1] + b * kE[0]) + rm * (kE[0] + b * kE[1])
    hi_b = (kA[1] + b * kA[0] + Hp) / cres; lo_b = -(kA[0] + b * kA[1] + Hm) / cres
    ceil = (kA[0] + kA[1]) / cres; alone = (kA[0] + kA[1]) / (GAMMA * S[0, 0])
    iA = np.arange(len(dA))
    # 41 ETF incumbents across the outer parallelotope's ETF extent (inner 90%)
    Mi0 = np.linalg.inv(GAMMA * S)
    bl = np.array([-(kA[0] + b * kA[1]), -(kE[0] + b * kE[1])]); bh = np.array([kA[1] + b * kA[0], kE[1] + b * kE[0]])
    VE = [(Mi0 @ np.array([x, y]))[1] for x in (bl[0], bh[0]) for y in (bl[1], bh[1])]
    jlo = int(np.clip(np.searchsorted(dE, 0.9 * min(VE)), 2 * sE, len(dE) - 1 - 2 * sE)); jhi = int(np.clip(np.searchsorted(dE, 0.9 * max(VE)), 2 * sE, len(dE) - 1 - 2 * sE))
    rows = np.unique(np.linspace(jlo, jhi, 41).astype(int))
    bands = []
    for j in rows:
        held = np.where(AA[:, j] == iA)[0]
        if held.size == 0:
            continue
        lo, hi = held.min(), held.max()
        contig = held.size == hi - lo + 1
        interior = lo > 3 * sA and hi < len(dA) - 1 - 3 * sA
        # ETF trade direction at each edge (at the fund's post-trade holding = the edge itself)
        def etf_dir(i):
            u = AE[i, j] - j
            return 1 if u > 0 else (-1 if u < 0 else 0)
        rec = dict(dE=float(dE[j]), lo=float(dA[lo]), hi=float(dA[hi]), contig=bool(contig), interior=bool(interior),
                   dir_lo=etf_dir(lo), dir_hi=etf_dir(hi))
        if last:
            cE = lambda d: kE[0] if d > 0 else (-kE[1] if d < 0 else None)
            if rec["dir_hi"] != 0:
                rec["f_hi"] = (kA[1] + rho * cE(rec["dir_hi"])) / cres
            if rec["dir_lo"] != 0:
                rec["f_lo"] = -(kA[0] - rho * cE(rec["dir_lo"])) / cres
        bands.append(rec)
    # reduced one-instrument band (part 3)
    h1 = np.where(A1 == iA)[0]
    red = (float(dA[h1.min()]), float(dA[h1.max()])) if h1.size else None
    # no-trade region and the outer parallelotope
    nt = (AA == iA[:, None]) & (AE == np.arange(len(dE))[None, :])
    ia, ie = np.nonzero(nt)
    inner = (ia > 3 * sA) & (ia < len(dA) - 1 - 3 * sA) & (ie > 3 * sE) & (ie < len(dE) - 1 - 3 * sE)
    ia, ie = ia[inner], ie[inner]
    X = np.stack([dA[ia], dE[ie]], 1)
    G = GAMMA * X @ S.T
    boxlo = np.array([-(kA[0] + b * kA[1]), -(kE[0] + b * kE[1])]); boxhi = np.array([kA[1] + b * kA[0], kE[1] + b * kE[0]])
    tolG = GAMMA * np.abs(S) @ np.array([hA, hE])
    outside = int(np.sum(np.any((G < boxlo - tolG) | (G > boxhi + tolG), axis=1)))
    rng = np.random.default_rng(t)
    if len(X) > 1:
        i1, i2 = rng.integers(0, len(X), 20000), rng.integers(0, len(X), 20000)
        ext = np.unique(np.concatenate([np.argsort(X[:, 0])[[0, -1]], np.argsort(X[:, 1])[[0, -1]]]))
        i1 = np.concatenate([i1, np.repeat(ext, len(ext))]); i2 = np.concatenate([i2, np.tile(ext, len(ext))])
        D = X[i1] - X[i2]
        lhs = GAMMA * np.einsum("pi,ij,pj->p", D, S, D)
        rhs = (kA[0] + kA[1]) * np.abs(D[:, 0]) + (kE[0] + kE[1]) * np.abs(D[:, 1])
        slack = GAMMA * (np.abs(S) @ np.array([hA, hE])) @ np.abs(D.T) * 2
        diam = float(np.max((lhs - rhs - slack) / np.maximum(rhs, 1e-300)))
        extA = (float(X[:, 0].min()), float(X[:, 0].max())); extE = (float(X[:, 1].min()), float(X[:, 1].max()))
    else:
        diam, extA, extE = None, None, None
    Mi = np.linalg.inv(GAMMA * S)
    V = np.array([Mi @ np.array([a, e]) for a in (boxlo[0], boxhi[0]) for e in (boxlo[1], boxhi[1])])
    return dict(t=t, bands=bands, reduced=red, hi_b=hi_b, lo_b=lo_b, ceil=ceil, alone=alone, nt_points=int(len(X)), outside=outside,
                diam=diam, extA=extA, extE=extE, parA=(float(V[:, 0].min()), float(V[:, 0].max())), parE=(float(V[:, 1].min()), float(V[:, 1].max())))


def convex_last(args):
    """Last review as a convex program (grid-free): the fund's band edges at an ETF incumbent, by bisection on d_A."""
    corr, kA, kE, pts = args                      # pts: (d_E, a seed inside the DP band)
    S, cres, rho = setup(corr, kA, kE)
    def fund_trade(a, e):
        u = cp.Variable(2); up, um = cp.Variable(2), cp.Variable(2)
        y = np.array([a, e]) + u
        obj = 0.5 * GAMMA * cp.quad_form(y, S) + kA[0] * up[0] + kA[1] * um[0] + kE[0] * up[1] + kE[1] * um[1]
        p = cp.Problem(cp.Minimize(1e4 * obj), [u == up - um, up >= 0, um >= 0]); p.solve(solver="CLARABEL")
        return float(u.value[0])
    out = []
    for e, seed in pts:
        edges = []
        if abs(fund_trade(seed, e)) > 1e-7:
            out.append(dict(dE=e, hi=None, lo=None, seed_held=False)); continue
        for side in (+1, -1):                         # from a held seed outward to the first traded point
            lo, hi = seed, seed + side * 20 * (kA[0] + kA[1]) / cres
            if abs(fund_trade(hi, e)) < 1e-9:
                edges.append(None); continue
            for _ in range(40):
                mid = 0.5 * (lo + hi)
                if abs(fund_trade(mid, e)) > 1e-7:
                    hi = mid
                else:
                    lo = mid
            edges.append(0.5 * (lo + hi))
        out.append(dict(dE=e, hi=edges[0], lo=edges[1], seed_held=True))
    return dict(corr=corr, kA=list(kA), kE=list(kE), rows=out)


def rounded(o):
    """Floats to 10 significant digits (grid quantities are exact multiples of h; tolerances are grid steps)."""
    if isinstance(o, float):
        return float(f"{o:.10g}")
    if isinstance(o, dict):
        return {k: rounded(v) for k, v in o.items()}
    if isinstance(o, list):
        return [rounded(v) for v in o]
    return o


def main():
    t0 = time.time(); S_ = {}
    fund = [(0.001, 0.001), (0.005, 0.005)]; etf = [(0.0, 0.0), (0.0002, 0.0002), (0.001, 0.001), (0.005, 0.005)]
    cells = [(c, kA, kE, r, st, 1) for c in (0.0, 0.5, 0.9, 0.97) for kA in fund for kE in etf for r in (-0.8, 0.0, 0.8) for st in (0.5, 0.1)]
    cells += [(c, (0.01, 0.0), (0.0005, 0.0005), r, st, 1) for c in (0.0, 0.5, 0.9, 0.97) for r in (-0.8, 0.0, 0.8) for st in (0.5, 0.1)]
    cells += [(0.97, (0.001, 0.001), (0.001, 0.001), 0.0, 0.5, 2), (0.5, (0.005, 0.005), (0.0002, 0.0002), 0.8, 0.1, 2),
              (0.97, (0.01, 0.0), (0.0005, 0.0005), 0.0, 0.5, 2), (0.97, (0.01, 0.0), (0.0005, 0.0005), 0.0, 0.5, 4)]
    with mp.Pool(6) as pool:
        S_["cells"] = pool.map(run_cell, cells, chunksize=1); print("dp", time.time() - t0, flush=True)
        conv = []
        for c in (0.97, 0.5):
            for kE in [(0.0002, 0.0002), (0.001, 0.001), (0.005, 0.005)]:
                cell = [x for x in S_["cells"] if x["corr"] == c and x["kA"] == [0.001, 0.001] and x["kE"] == list(kE) and x["r"] == 0.0 and x["step"] == 0.5 and x["hfac"] == 1][0]
                b = cell["rows"][-1]["bands"]; pick = [(b[k]["dE"], 0.5 * (b[k]["lo"] + b[k]["hi"])) for k in np.linspace(0, len(b) - 1, 10).astype(int)]
                conv.append((c, (0.001, 0.001), kE, pick))
        S_["convex"] = pool.map(convex_last, conv); print("convex", time.time() - t0, flush=True)
    S_["seconds"] = time.time() - t0
    S_ = json.loads(json.dumps(S_, default=lambda o: o.tolist() if hasattr(o, "tolist") else (int(o) if isinstance(o, np.integer) else float(o))))
    json.dump(rounded(S_), open(HERE / "summary.json", "w"), separators=(",", ":"))
    print("done", S_["seconds"])


if __name__ == "__main__":
    main()
