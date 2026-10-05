"""Experiment 039: the D15c mixture reading (the r-effect in re-hedge-regime bands by remaining reviews, and against the
future-idle share). Registered design: experiments/039-rehedge-mixture-reading.md.
Run: uv run python experiments/039/analyze.py

Item 1 reads experiment 036's summary.json. Item 2 reruns 036's r = 0 cells (036's own grid and code path, no new
cells), keeps the policy arrays, and propagates the exact state distribution along the target lattice.
"""
import importlib.util
import json
import multiprocessing as mp
import sys
import time
from collections import defaultdict
from pathlib import Path

import numpy as np
from scipy.stats import spearmanr

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("run036", HERE.parent / "036" / "run.py")
m36 = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(m36)
sys.path.insert(0, str(HERE.parent / "023"))
import fastdp  # noqa: E402

T, GAMMA, BETA, SEE = m36.T, m36.GAMMA, m36.BETA, m36.SEE


def good(b):
    return b["interior"] and b["contig"]


def regime(b):
    return "idle" if (b["dir_lo"] == 0 and b["dir_hi"] == 0) else ("re-hedge" if (b["dir_lo"] != 0 and b["dir_hi"] != 0) else "mixed")


def pairs_from_036():
    S = json.load(open(HERE.parent / "036" / "summary.json"))
    cells = [c for c in S["cells"] if c["hfac"] == 1 and c["kE"] != [0.0, 0.0] and c["corr"] > 0]
    by = defaultdict(dict)
    for c in cells:
        by[(c["corr"], tuple(c["kA"]), tuple(c["kE"]), c["step"])][c["r"]] = c
    out = []
    for k, d in by.items():
        c0 = d[0.0]
        for r in (-0.8, 0.8):
            c1 = d[r]
            for t in range(7):
                b0 = {round(b["dE"], 12): b for b in c0["rows"][t]["bands"] if good(b)}
                b1 = {round(b["dE"], 12): b for b in c1["rows"][t]["bands"] if good(b)}
                ceil = c0["rows"][t]["ceil"]
                for e, a in b0.items():
                    b = b1.get(e)
                    if b is None or regime(a) != "re-hedge" or regime(b) != "re-hedge":
                        continue
                    w0, w1 = a["hi"] - a["lo"], b["hi"] - b["lo"]
                    if w0 <= 0 or w1 <= 0 or w0 / ceil >= 0.9:
                        continue
                    L = abs(np.log(w1 / w0))
                    out.append(dict(key=list(k), r=r, t=t, dE=e, lo=a["lo"], hi=a["hi"], abslog=L, moved=bool(L > 2 * c0["hA"] / w0)))
    return out


def rerun(key):
    """036's run_cell at r = 0, keeping AA and AE per review; returns the future-idle share per (t, sampled row)."""
    corr, kA, kE, step = key[0], tuple(key[1]), tuple(key[2]), key[3]
    S, cres, rho = m36.setup(corr, kA, kE)
    vmin, vmax = m36.extent(S, kA, kE)
    span = (vmax - vmin) * 1.2
    wA = (kA[0] + kA[1]) / cres
    wE = (kE[0] + kE[1]) / (GAMMA * SEE) if kE[0] + kE[1] > 0 else 2 * 0.001 / (GAMMA * SEE)
    uA, uE = step * wA, step * wE
    hA = max(wA / 100, 1.4 * span[0] / m36.CAP); hE = max(wE / 100, 1.4 * span[1] / m36.CAP)
    sA, sE = max(1, round(uA / hA)), max(1, round(uE / hE))
    mA = int(np.ceil((max(-vmin[0], vmax[0]) * 1.2 + 3 * sA * hA) / hA)); mE = int(np.ceil((max(-vmin[1], vmax[1]) * 1.2 + 3 * sE * hE) / hE))
    dA = np.arange(-mA, mA + 1) * hA; dE = np.arange(-mE, mE + 1) * hE
    nA, nE = len(dA), len(dE)
    YA, YE = np.meshgrid(dA, dE, indexing="ij")
    quad = -0.5 * GAMMA * (S[0, 0] * YA ** 2 + 2 * S[0, 1] * YA * YE + S[1, 1] * YE ** 2)
    law = [((+1, +1), 0.25), ((-1, -1), 0.25), ((+1, -1), 0.25), ((-1, +1), 0.25)]
    V = np.zeros_like(quad); AAs = [None] * T; AEs = [None] * T
    for t in range(T - 1, -1, -1):
        cont = np.zeros_like(V)
        if t < T - 1:
            P = np.pad(V, ((sA, sA), (sE, sE)), mode="edge")
            for (a, e), pr in law:
                cont += pr * P[sA - a * sA: sA - a * sA + nA, sE - e * sE: sE - e * sE + nE]
        W = quad + BETA * cont
        Z, AE = fastdp.l1(W, kE[0] * hE, kE[1] * hE, axis=1)
        U, AA = fastdp.l1(Z, kA[0] * hA, kA[1] * hA, axis=0)
        V = U; AAs[t] = AA.astype(np.int32); AEs[t] = AE.astype(np.int32)
    iA = np.arange(nA)
    idle = []; edges = []
    for s in range(T):
        held = AAs[s] == iA[:, None]
        has = held.any(0)
        lo = np.where(has, held.argmax(0), -1); hi = np.where(has, nA - 1 - held[::-1].argmax(0), -1)
        cols = np.arange(nE)
        dlo = np.where(has, AEs[s][np.clip(lo, 0, nA - 1), cols] - cols, 1); dhi = np.where(has, AEs[s][np.clip(hi, 0, nA - 1), cols] - cols, 1)
        idle.append(has & (dlo == 0) & (dhi == 0)); edges.append((lo, hi))
    shares = {}
    for t in range(7):
        lo_t, hi_t = edges[t]
        for j in range(nE):
            pass
    return dict(key=key, hA=hA, hE=hE, mE=mE, nA=nA, nE=nE, sA=sA, sE=sE), AAs, AEs, idle, edges


def future_idle(AAs, AEs, idle, t, i_edge, j0, nA, nE, sA, sE):
    """Exact distribution along the lattice from the post-trade state at review t; average P(idle row) over t+1..T-1."""
    i_post, j_post = int(i_edge), int(AEs[t][i_edge, j0])
    states = np.array([[i_post, j_post]]); prob = np.array([1.0]); ps = []
    for s in range(t + 1, T):
        nxt = []; pn = []
        for (a, e) in ((1, 1), (-1, -1), (1, -1), (-1, 1)):
            nxt.append(np.stack([np.clip(states[:, 0] - a * sA, 0, nA - 1), np.clip(states[:, 1] - e * sE, 0, nE - 1)], 1)); pn.append(prob * 0.25)
        st = np.concatenate(nxt); pr = np.concatenate(pn)
        lin = st[:, 0] * nE + st[:, 1]
        u, inv = np.unique(lin, return_inverse=True)
        prob = np.bincount(inv, weights=pr); states = np.stack([u // nE, u % nE], 1)
        ps.append(float(np.sum(prob * idle[s][states[:, 1]])))
        # apply review s's policy to get the post-trade states
        a_post = AAs[s][states[:, 0], states[:, 1]]
        e_post = AEs[s][a_post, states[:, 1]]
        lin = a_post * nE + e_post
        u, inv = np.unique(lin, return_inverse=True)
        prob = np.bincount(inv, weights=prob); states = np.stack([u // nE, u % nE], 1)
    return float(np.mean(ps))


def cell_shares(args):
    key, want = args                                  # want: list of (t, dE, lo, hi)
    info, AAs, AEs, idle, edges = rerun(key)
    out = []
    for t, e, lo, hi in want:
        j0 = int(round(e / info["hE"])) + info["mE"]
        # the rerun reproduces 036's recorded edges (grid units)
        lo_r, hi_r = edges[t][0][j0], edges[t][1][j0]
        mism = max(abs(lo_r - (int(round(lo / info["hA"])) + (info["nA"] - 1) // 2)), abs(hi_r - (int(round(hi / info["hA"])) + (info["nA"] - 1) // 2)))
        vals = []
        for x in (lo, hi):
            i_e = int(round(x / info["hA"])) + (info["nA"] - 1) // 2
            vals.append(future_idle(AAs, AEs, idle, t, i_e, j0, info["nA"], info["nE"], info["sA"], info["sE"]))
        out.append((t, e, float(np.mean(vals)), int(mism)))
    return key, out


def main():
    t0 = time.time()
    P = pairs_from_036()
    print(f"{len(P)} re-hedge pairs (corr > 0, not coarse, t < 7)")
    # item 1
    tab = defaultdict(list)
    for p in P:
        tab[(p["key"][0], p["key"][3], p["t"])].append(p)
    rows1 = []
    print("\n| corr | step | t | pairs | share moved | median |log ratio| |")
    print("|---|---|---|---|---|---|")
    for (corr, st, t), ps in sorted(tab.items()):
        sm = float(np.mean([p["moved"] for p in ps])); ml = float(np.median([p["abslog"] for p in ps]))
        rows1.append(dict(corr=corr, step=st, t=t, n=len(ps), share_moved=sm, median_abslog=ml))
        print(f"| {corr} | {st} | {t} | {len(ps)} | {sm:.2f} | {ml:.4f} |")
    rho1 = spearmanr([7 - r["t"] for r in rows1], [r["share_moved"] for r in rows1])
    print(f"\n- Spearman(share moved, remaining reviews 7 - t) over {len(rows1)} (corr, step, t) cells: {rho1.correlation:+.3f} (p {rho1.pvalue:.1e})")
    # item 2
    want = defaultdict(set)
    for p in P:
        want[tuple(map(lambda v: tuple(v) if isinstance(v, list) else v, p["key"]))].add((p["t"], p["dE"], p["lo"], p["hi"]))
    with mp.Pool(4) as pool:
        res = pool.map(cell_shares, [([k[0], list(k[1]), list(k[2]), k[3]], sorted(v)) for k, v in want.items()])
    share = {}; mism = 0
    for key, out in res:
        for t, e, sh, mm in out:
            share[(key[0], tuple(key[1]), tuple(key[2]), key[3], t, e)] = sh; mism = max(mism, mm)
    print(f"\n- rerun reproduces 036's recorded band edges: largest mismatch {mism} grid steps")
    for p in P:
        p["share"] = share[(p["key"][0], tuple(p["key"][1]), tuple(p["key"][2]), p["key"][3], p["t"], p["dE"])]
    rho2 = spearmanr([p["share"] for p in P], [p["abslog"] for p in P])
    print(f"\n- Spearman(|log ratio|, future-idle share) over {len(P)} re-hedge pairs: {rho2.correlation:+.3f} (p {rho2.pvalue:.1e})")
    rows2 = []                                         # Deviation 1: fixed bins (over half the shares are exactly 0)
    print("\n| future-idle share | pairs | share moved | median |log ratio| | mean |log ratio| |")
    print("|---|---|---|---|---|")
    for lo_, hi_, lab in ((0, 0, "0"), (0, 0.1, "(0, 0.1]"), (0.1, 0.3, "(0.1, 0.3]"), (0.3, 0.6, "(0.3, 0.6]"), (0.6, 1.0, "(0.6, 1]")):
        ps = [p for p in P if (p["share"] == 0 if lab == "0" else lo_ < p["share"] <= hi_)]
        if not ps:
            continue
        sm = float(np.mean([p["moved"] for p in ps])); ml = float(np.median([p["abslog"] for p in ps])); mn = float(np.mean([p["abslog"] for p in ps]))
        rows2.append(dict(bin=lab, n=len(ps), share_moved=sm, median_abslog=ml, mean_abslog=mn))
        print(f"| {lab} | {len(ps)} | {sm:.2f} | {ml:.4f} | {mn:.4f} |")
    # within t (controls for remaining reviews)
    within = []
    for t in range(7):
        ps = [p for p in P if p["t"] == t]
        if len(ps) > 20 and np.ptp([p["share"] for p in ps]) > 0:
            within.append((t, len(ps), float(spearmanr([p["share"] for p in ps], [p["abslog"] for p in ps]).correlation)))
    print("\n- Spearman within each review t: " + "; ".join(f"t={t}: {c:+.2f} ({n})" for t, n, c in within))
    json.dump(dict(n_pairs=len(P), item1=rows1, spearman_t=float(rho1.correlation), item2=rows2, spearman_share=float(rho2.correlation),
                   within_t=within, seconds=time.time() - t0), open(HERE / "summary.json", "w"), indent=1)
    import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    fig, axes = plt.subplots(1, 2, figsize=(10, 4))
    for (corr, st), col in zip([(0.5, 0.1), (0.5, 0.5), (0.9, 0.1), (0.9, 0.5), (0.97, 0.1), (0.97, 0.5)], ["C0", "C1", "C2", "C3", "C4", "C5"]):
        rs = sorted([r for r in rows1 if r["corr"] == corr and r["step"] == st], key=lambda r: r["t"])
        axes[0].plot([r["t"] for r in rs], [r["share_moved"] for r in rs], "o-", color=col, ms=3, label=f"corr {corr}, step {st}")
    axes[0].set_xlabel("review t (7 - t reviews remain)"); axes[0].set_ylabel("share of re-hedge pairs moved by r"); axes[0].legend(fontsize=6)
    axes[1].plot([p["share"] for p in P], [p["abslog"] for p in P], ".", ms=1.5, color="0.4")
    axes[1].set_xlabel("future-idle share"); axes[1].set_ylabel("|log width ratio|"); axes[1].set_title(f"Spearman {rho2.correlation:+.2f}")
    fig.tight_layout(); fig.savefig(HERE / "fig_mixture.png", dpi=130); plt.close(fig)
    print(f"\nseconds {time.time() - t0:.0f}")


if __name__ == "__main__":
    main()
