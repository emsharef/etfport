"""Experiment 021 Part 1: the exact reference. Registered design: experiments/021-dp-reference.md (Deviation 1).

Run:    uv run python experiments/021/run.py          (writes experiments/021/results.json)
Report: uv run python experiments/021/run.py report
"""
import json
import os
import sys
import time
from multiprocessing import Pool
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import griddp  # noqa: E402
import riccati  # noqa: E402
from model import KAPPA, LAMBDA, Inst, cost_vec  # noqa: E402

GAMMAS, TS = (2.0, 5.0, 10.0), (4, 8)
Q_SPECS = {"Q1": (1, 1, 1, [0], False), "Q2": (2, 1, 1, [0, 1], True), "Q3": (3, 2, 2, [0, 1, 2], True)}
P_SPECS = {"P1": (1, 1, 1, [0], False), "P2": (2, 1, 1, [0], False)}


def incumbent(I):
    return np.array([0.3 / I.N] * I.N + [0.3 / I.M] * I.M)


def mgrid(I):
    sd = np.sqrt(I.P(0)[0, 0] - I.P(I.T)[0, 0])
    return I.m0()[0] + np.linspace(-4, 4, 41) * sd


# ---------------------------------------------------------------- quadratic: Riccati
def riccati_task(key):
    name, g, T = key
    I = Inst(name, *Q_SPECS[name], g, T)
    pol, M, c = riccati.solve(I)
    m0 = I.m0()
    out = dict(inst=name, gamma=g, T=T, resid=max(p["resid"] for p in pol), per_t=[])
    for t, p in enumerate(pol):
        full, ap, ep = riccati.aim(I, p, m0)
        out["per_t"].append(dict(t=t, Kx=p["Kx"].tolist(), Km=p["Km"].tolist(), k0=p["k0"].tolist(),
                                 speed=np.diag(np.eye(I.n) - p["Kx"]).tolist(),
                                 aim=full.tolist(), aim_alpha=ap.tolist(), aim_exposure=ep.tolist(),
                                 alpha_sd=np.sqrt(np.diag(I.P(t))[:I.N]).tolist(), innov_sd=np.sqrt(np.clip(np.diag(I.Q(t))[:I.N], 0, None)).tolist()))
    for lab, x in (("V0_zero", np.zeros(I.n)), ("V0_incumbent", incumbent(I))):
        out[lab] = riccati.value(M, c, np.concatenate([x, m0, [1.0]])) * 1e4 / T     # bp per quarter
    return out


# ---------------------------------------------------------------- grids
def hgrid(lo, hi, h):
    return np.round(np.arange(round((hi - lo) / h) + 1) * h + lo, 12)


def q1_box(I, pol, pad=0.5):
    """Deviation 2: a box containing the Riccati aim portfolio at the extreme belief grid points in every quarter."""
    mg = mgrid(I)
    lo, hi = np.full(I.n, np.inf), np.full(I.n, -np.inf)
    for p in pol:
        for mv in (mg[0], mg[-1]):
            m = I.m0().copy(); m[0] = mv
            a, _, _ = riccati.aim(I, p, m)
            lo, hi = np.minimum(lo, a), np.maximum(hi, a)
    return lo, hi, lo - pad, hi + pad


def q1_grid_task(key):
    g, T, h = key
    I = Inst("Q1", *Q_SPECS["Q1"], g, T)
    pol, M, c = riccati.solve(I)
    ilo, ihi, blo, bhi = q1_box(I, pol)
    grids = [hgrid(np.floor(blo[k] / h) * h, np.ceil(bhi[k] / h) * h, h) for k in range(2)]
    mg = mgrid(I)
    V, pols = griddp.solve(I, grids, cost_vec(I, LAMBDA), "quad", mg)
    # compare inside the aims' hull, at belief points within 2 sd of the prior mean
    X0, X1 = np.meshgrid(*grids, indexing="ij")
    inner = (X0 >= ilo[0]) & (X0 <= ihi[0]) & (X1 >= ilo[1]) & (X1 <= ihi[1])
    sd = np.sqrt(I.P(0)[0, 0] - I.P(I.T)[0, 0])
    dv, dp = 0.0, 0.0
    for j, mv in enumerate(mg):
        if abs(mv - I.m0()[0]) > 2 * sd:
            continue
        m = I.m0().copy(); m[0] = mv
        s = np.stack([X0, X1, np.full_like(X0, m[0]), np.full_like(X0, m[1]), np.ones_like(X0)], -1)
        Vr = np.einsum("...i,ij,...j->...", s, M, s) + c
        dv = max(dv, np.abs(V[..., j] - Vr)[inner].max())
        p = pol[0]
        xr = np.einsum("ij,...j->...i", np.hstack([p["Kx"], p["Km"], p["k0"][:, None]]), s)
        yg = np.stack([grids[k][pols[0][k][..., j]] for k in range(2)], -1)
        dp = max(dp, np.abs(yg - xr)[inner].max())
    return dict(gamma=g, T=T, h=h, box=[[float(grids[k][0]), float(grids[k][-1])] for k in range(2)],
                max_value_diff_bp_total=dv * 1e4, max_value_diff_bp_q=dv * 1e4 / T, max_policy_diff=dp)


def bands(I, grids, pols, pols0, mg):
    """No-trade band per instrument along the line through the frictionless target (other instruments held at
    their target), per t and belief grid point where every target is strictly inside the caps."""
    out = []
    n = I.n
    for t in range(I.T):
        y, y0 = pols[t], pols0[t]
        for j in range(len(mg)):
            tgt = [int(y0[k][(0,) * n + (j,)]) for k in range(n)]
            G = [len(g) for g in grids]
            if all(tg in (0, Gk - 1) for tg, Gk in zip(tgt, G)):
                continue
            rec = dict(t=t, m=float(mg[j]), m_index=j, target=[float(grids[k][tgt[k]]) for k in range(n)], edges=[])
            for i in range(n):
                idx = list(tgt) + [j]
                line = []
                for xi in range(G[i]):
                    idx[i] = xi
                    line.append(int(y[i][tuple(idx)]) == xi)
                lo = hi = tgt[i]
                if tgt[i] in (0, G[i] - 1) or not line[tgt[i]]:     # Deviation 2: only where this target is interior
                    rec["edges"].append(None); continue
                while lo - 1 >= 0 and line[lo - 1]:
                    lo -= 1
                while hi + 1 < G[i] and line[hi + 1]:
                    hi += 1
                rec["edges"].append([float(grids[i][lo]), float(grids[i][hi]), lo == 0, hi == G[i] - 1])
            out.append(rec)
    return out


def p_task(key):
    name, g, T, h, kf, ke = key
    I = Inst(name, *P_SPECS[name], g, T)
    grids = [hgrid(0.0, 1.0, h)] * I.n
    mg = mgrid(I)
    kap = np.array([kf] * I.N + [ke] * I.M)
    V, pols = griddp.solve(I, grids, kap, "l1", mg)
    V0, pols0 = griddp.solve(I, grids, np.zeros(I.n), "l1", mg)
    j0 = int(np.argmin(np.abs(mg - I.m0()[0])))
    def val(x):
        idx = tuple(int(round(v / h)) for v in x) + (j0,)
        return float(V[idx]) * 1e4 / T
    return dict(inst=name, gamma=g, T=T, h=h, kappa_fund=kf, kappa_etf=ke,
                V0_zero=val(np.zeros(I.n)), V0_incumbent=val(incumbent(I)),
                innov_sd=[float(np.sqrt(I.Q(t)[0, 0])) for t in range(T)], mgrid=mg.tolist(),
                bands=bands(I, grids, pols, pols0, mg))


def run():
    t0 = time.time()
    tasks_r = [(nm, g, T) for nm in Q_SPECS for g in GAMMAS for T in TS]
    tasks_q1 = [(g, T, 1 / 50) for g in (5.0, 10.0) for T in TS] + [(5.0, 4, 1 / 25), (10.0, 4, 1 / 100)]   # Deviation 2
    tasks_p = [("P1", g, T, h, KAPPA["fund"], KAPPA["etf"]) for g in GAMMAS for T in TS for h in (1 / 50, 1 / 100, 1 / 200)]
    tasks_p += [("P1", 5.0, 4, h, k, k) for k in (0.0005, 0.002, 0.01) for h in (1 / 100, 1 / 200)]   # kappa sweep
    tasks_p += [("P2", g, T, h, KAPPA["fund"], KAPPA["etf"]) for g in GAMMAS for T in TS for h in (1 / 20, 1 / 40)]
    procs = int(os.environ.get("PROCS", "8"))
    with Pool(procs) as pool:
        ric = pool.map(riccati_task, tasks_r)
        q1 = pool.map(q1_grid_task, tasks_q1, chunksize=1)
        pg = pool.map(p_task, tasks_p, chunksize=1)
    (HERE / "results.json").write_text(json.dumps(dict(riccati=ric, q1_grid=q1, prop=pg)))
    print(f"seconds: {time.time() - t0:.0f}")


if __name__ == "__main__":
    if sys.argv[1:] == ["report"]:
        import report
        report.main()
    else:
        run()
