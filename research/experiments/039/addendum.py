"""Experiment 039, Deviation 3 (addendum at mathb's request, note 2026-09-29-d15c-innovation-corr-restated):
(i) the one-remaining-review control; (ii) median |log ratio| by remaining reviews and regime, and the re-hedge r-effect
against the next-review idle probability; (iii) the idle regime's cube-root slope by the future-idle share.
Run: uv run python experiments/039/addendum.py   (reads 036's summary.json; reruns 036's r = 0 cells as analyze.py does)
"""
import importlib.util
import json
import multiprocessing as mp
from collections import defaultdict
from pathlib import Path

import numpy as np
from scipy.stats import spearmanr

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("a039", HERE / "analyze.py")
a39 = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(a39)
SEE, SAA = 0.0854 ** 2, 0.0854 ** 2 + 0.02 ** 2
T = a39.T


def all_pairs():
    S = json.load(open(HERE.parent / "036" / "summary.json"))
    cells = [c for c in S["cells"] if c["hfac"] == 1 and c["kE"] != [0.0, 0.0] and c["corr"] > 0]
    by = defaultdict(dict)
    for c in cells:
        by[(c["corr"], tuple(c["kA"]), tuple(c["kE"]), c["step"])][c["r"]] = c
    out = []
    for k, d in by.items():
        c0 = d[0.0]
        uA, uE = c0["sA"] * c0["hA"], c0["sE"] * c0["hE"]; rhoAB = c0["rho"] * SEE / SAA
        vi = lambda r: uA ** 2 + rhoAB ** 2 * uE ** 2 + 2 * rhoAB * r * uA * uE
        for r in (-0.8, 0.8):
            c1 = d[r]
            for t in range(T):
                b0 = {round(b["dE"], 12): b for b in c0["rows"][t]["bands"] if a39.good(b)}
                b1 = {round(b["dE"], 12): b for b in c1["rows"][t]["bands"] if a39.good(b)}
                ceil, alone = c0["rows"][t]["ceil"], c0["rows"][t]["alone"]
                for e, a in b0.items():
                    b = b1.get(e)
                    if b is None or a39.regime(a) != a39.regime(b):
                        continue
                    w0, w1 = a["hi"] - a["lo"], b["hi"] - b["lo"]
                    if w0 <= 0 or w1 <= 0:
                        continue
                    out.append(dict(key=[k[0], list(k[1]), list(k[2]), k[3]], r=r, t=t, dE=e, lo=a["lo"], hi=a["hi"], regime=a39.regime(a),
                                    abslog=abs(float(np.log(w1 / w0))), logobs=float(np.log(w1 / w0)), logpred=float(np.log((vi(r) / vi(0.0)) ** (1 / 3))),
                                    res=c0["hA"] / w0, coarse=w0 / ceil >= 0.9, alone_frac=w0 / alone))
    return out


def shares(args):
    key, want = args
    info, AAs, AEs, idle, edges = a39.rerun(key)
    out = []
    for t, e, lo, hi in want:
        j0 = int(round(e / info["hE"])) + info["mE"]
        nxt, allp = [], []
        for x in (lo, hi):
            i_e = int(round(x / info["hA"])) + (info["nA"] - 1) // 2
            ps = path_probs(AAs, AEs, idle, t, i_e, j0, info["nA"], info["nE"], info["sA"], info["sE"])
            nxt.append(ps[0]); allp.append(np.mean(ps))
        out.append((t, e, float(np.mean(nxt)), float(np.mean(allp))))
    return key, out


def path_probs(AAs, AEs, idle, t, i_edge, j0, nA, nE, sA, sE):
    i_post, j_post = int(i_edge), int(AEs[t][i_edge, j0])
    states = np.array([[i_post, j_post]]); prob = np.array([1.0]); ps = []
    for s in range(t + 1, T):
        nx, pn = [], []
        for (a, e) in ((1, 1), (-1, -1), (1, -1), (-1, 1)):
            nx.append(np.stack([np.clip(states[:, 0] - a * sA, 0, nA - 1), np.clip(states[:, 1] - e * sE, 0, nE - 1)], 1)); pn.append(prob * 0.25)
        st = np.concatenate(nx); pr = np.concatenate(pn)
        u, inv = np.unique(st[:, 0] * nE + st[:, 1], return_inverse=True)
        prob = np.bincount(inv, weights=pr); states = np.stack([u // nE, u % nE], 1)
        ps.append(float(np.sum(prob * idle[s][states[:, 1]])))
        a_post = AAs[s][states[:, 0], states[:, 1]]; e_post = AEs[s][a_post, states[:, 1]]
        u, inv = np.unique(a_post * nE + e_post, return_inverse=True)
        prob = np.bincount(inv, weights=prob); states = np.stack([u // nE, u % nE], 1)
    return ps


def main():
    P = all_pairs()
    # (i) one remaining review
    last = [p for p in P if p["t"] == T - 1]
    print(f"(i) one remaining review: {len(last)} pairs (all regimes); largest |log ratio| {max(p['abslog'] for p in last):.2e}; "
          f"in grid steps (|log| / resolution) largest {max(p['abslog'] / p['res'] for p in last):.2f}")
    # (ii) table by remaining reviews and regime (not coarse)
    print("\n(ii) median |log ratio| (share moved beyond two grid steps) by remaining reviews 7 - t and regime; corr > 0, ETF rate > 0, not coarse")
    print("| remaining reviews | idle (fine) | re-hedge | mixed |")
    print("|---|---|---|---|")
    tab = []
    for t in range(T - 1, -1, -1):
        row = [f"| {T - t} "]
        for reg in ("idle", "re-hedge", "mixed"):
            ps = [p for p in P if p["t"] == t and p["regime"] == reg and not p["coarse"] and (reg != "idle" or p["alone_frac"] < 0.9)]
            if ps:
                m = float(np.median([p["abslog"] for p in ps])); sm = float(np.mean([p["abslog"] > 2 * p["res"] for p in ps]))
                row.append(f"| {m:.4f} ({sm:.2f}; n {len(ps)}) "); tab.append(dict(remaining=T - t, regime=reg, median=m, share_moved=sm, n=len(ps)))
            else:
                row.append("| - ")
        print("".join(row) + "|")
    # (ii) and (iii) shares
    want = defaultdict(set)
    sel = [p for p in P if p["t"] < T - 1 and not p["coarse"] and (p["regime"] == "re-hedge" or (p["regime"] == "idle" and p["alone_frac"] < 0.9 and abs(p["logpred"]) > 0.01))]
    for p in sel:
        want[(p["key"][0], tuple(p["key"][1]), tuple(p["key"][2]), p["key"][3])].add((p["t"], p["dE"], p["lo"], p["hi"]))
    with mp.Pool(4) as pool:
        res = pool.map(shares, [([k[0], list(k[1]), list(k[2]), k[3]], sorted(v)) for k, v in want.items()])
    sh = {}
    for key, out in res:
        for t, e, nx, al in out:
            sh[(key[0], tuple(key[1]), tuple(key[2]), key[3], t, e)] = (nx, al)
    for p in sel:
        p["next_idle"], p["all_idle"] = sh[(p["key"][0], tuple(p["key"][1]), tuple(p["key"][2]), p["key"][3], p["t"], p["dE"])]
    rh = [p for p in sel if p["regime"] == "re-hedge"]
    s_next = spearmanr([p["next_idle"] for p in rh], [p["abslog"] for p in rh]).correlation
    s_all = spearmanr([p["all_idle"] for p in rh], [p["abslog"] for p in rh]).correlation
    sgn = [p for p in rh if p["abslog"] > 2 * p["res"]]
    print(f"\n(ii) re-hedge: Spearman(|log ratio|, next-review idle probability) {s_next:+.3f}; with the whole-continuation share (039) {s_all:+.3f}; "
          f"sign of log ratio = sign of r Sigma_AE among {len(sgn)} moved: {np.mean([np.sign(p['logobs']) == np.sign(p['r']) for p in sgn]):.2f}")
    bins = [(0, 0), (0, 0.25), (0.25, 0.5), (0.5, 0.75), (0.75, 1.0)]
    print("| next-review idle probability | pairs | median |log ratio| | share moved |")
    print("|---|---|---|---|")
    tb2 = []
    for lo, hi in bins:
        ps = [p for p in rh if (p["next_idle"] == 0 if hi == 0 else lo < p["next_idle"] <= hi)]
        if ps:
            m = float(np.median([p["abslog"] for p in ps])); sm = float(np.mean([p["abslog"] > 2 * p["res"] for p in ps]))
            tb2.append(dict(lo=lo, hi=hi, n=len(ps), median=m, share_moved=sm))
            print(f"| {'0' if hi == 0 else f'({lo}, {hi}]'} | {len(ps)} | {m:.4f} | {sm:.2f} |")
    # (iii) idle regime: slope of log obs on log pred by the future-idle share
    idl = [p for p in sel if p["regime"] == "idle"]
    print(f"\n(iii) idle regime, fine, corr > 0 ({len(idl)} pairs): slope of log observed on log predicted by whole-continuation idle share")
    print("| future-idle share | pairs | slope | median |log obs - log pred| |")
    print("|---|---|---|---|")
    tb3 = []
    for lo, hi in ((0, 0.5), (0.5, 0.75), (0.75, 0.9), (0.9, 1.0)):
        ps = [p for p in idl if lo <= p["all_idle"] <= hi and (hi == 1.0 or p["all_idle"] < hi)]
        if len(ps) > 5 and np.ptp([p["logpred"] for p in ps]) > 1e-9:
            sl = float(np.polyfit([p["logpred"] for p in ps], [p["logobs"] for p in ps], 1)[0]); me = float(np.median([abs(p["logobs"] - p["logpred"]) for p in ps]))
            tb3.append(dict(lo=lo, hi=hi, n=len(ps), slope=sl, med_err=me))
            print(f"| [{lo}, {hi}] | {len(ps)} | {sl:.2f} | {me:.4f} |")
    rho3 = spearmanr([p["all_idle"] for p in idl], [abs(p["logobs"] - p["logpred"]) for p in idl]).correlation
    print(f"- Spearman(|log obs - log pred|, future-idle share) over idle pairs: {rho3:+.3f}")
    json.dump(dict(control_last=dict(n=len(last), max_abslog=max(p["abslog"] for p in last)), by_remaining=tab, rehedge_next=dict(spearman_next=float(s_next), spearman_all=float(s_all), bins=tb2),
                   idle_slope=tb3, idle_err_spearman=float(rho3)), open(HERE / "addendum.json", "w"), indent=1)


if __name__ == "__main__":
    main()
