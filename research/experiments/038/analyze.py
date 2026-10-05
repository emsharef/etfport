"""Experiment 038: mathb's innovation-correlation conjecture read on experiment 036's recorded bands (no new run).
Registered design: experiments/038-innovation-corr-reading.md.  Run: uv run python experiments/038/analyze.py
"""
import json
from collections import defaultdict
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
S36 = json.load(open(HERE.parent / "036" / "summary.json"))
SEE, SAA = 0.0854 ** 2, 0.0854 ** 2 + 0.02 ** 2


def good(b):
    return b["interior"] and b["contig"]


def regime(b):
    if b["dir_lo"] == 0 and b["dir_hi"] == 0:
        return "idle"
    if b["dir_lo"] != 0 and b["dir_hi"] != 0:
        return "re-hedge"
    return "mixed"


def main():
    cells = [c for c in S36["cells"] if c["hfac"] == 1 and c["kE"] != [0.0, 0.0]]
    key = lambda c: (c["corr"], tuple(c["kA"]), tuple(c["kE"]), c["step"])
    by = defaultdict(dict)
    for c in cells:
        by[key(c)][c["r"]] = c
    pairs = []
    for k, d in by.items():
        if 0.0 not in d:
            continue
        c0 = d[0.0]
        uA, uE = c0["sA"] * c0["hA"], c0["sE"] * c0["hE"]
        rhoAB = c0["rho"] * SEE / SAA
        vi = lambda r: uA ** 2 + rhoAB ** 2 * uE ** 2 + 2 * rhoAB * r * uA * uE
        for r in (-0.8, 0.8):
            if r not in d:
                continue
            c1 = d[r]
            for t in range(7):
                b0 = {round(b["dE"], 12): b for b in c0["rows"][t]["bands"] if good(b)}
                b1 = {round(b["dE"], 12): b for b in c1["rows"][t]["bands"] if good(b)}
                ceil = c0["rows"][t]["ceil"]
                for e, a in b0.items():
                    b = b1.get(e)
                    if b is None or regime(a) != regime(b):
                        continue
                    w0, w1 = a["hi"] - a["lo"], b["hi"] - b["lo"]
                    if w0 <= 0 or w1 <= 0:
                        continue
                    reg = regime(a)
                    pred = (vi(r) / vi(0.0)) ** (1 / 3) if reg == "idle" else 1.0
                    frac = w0 / ceil
                    pairs.append(dict(corr=k[0], kA=k[1][0], kE=k[2][0], step=k[3], r=r, t=t, regime=reg,
                                      fine=frac < 0.5, coarse=frac >= 0.9, obs=w1 / w0, pred=pred, res=c0["hA"] / w0,
                                      alone_frac=w0 / c0["rows"][t]["alone"]))
    out = {"n_pairs": len(pairs), "table": []}
    print(f"{len(pairs)} pairs (r = +-0.8 against r = 0; t < 7; ETF rate > 0)\n")
    print("| regime | fineness | step | pairs | median abs log err (prediction) | 90th pct | median abs log err (null: ratio 1) | within resolution (prediction) | slope of log obs on log pred |")
    print("|---|---|---|---|---|---|---|---|---|")
    for reg in ("idle", "re-hedge", "mixed"):
        for fn, sel in (("fine", lambda p: p["fine"]), ("middle", lambda p: not p["fine"] and not p["coarse"]), ("coarse", lambda p: p["coarse"])):
            for st in (0.1, 0.5):
                ps = [p for p in pairs if p["regime"] == reg and sel(p) and p["step"] == st]
                if not ps:
                    continue
                le = np.abs(np.log([p["obs"] for p in ps]) - np.log([p["pred"] for p in ps]))
                ln = np.abs(np.log([p["obs"] for p in ps]))
                within = np.mean([abs(p["obs"] - p["pred"]) <= p["res"] * (1 + p["obs"]) for p in ps])
                x = np.log([p["pred"] for p in ps]); y = np.log([p["obs"] for p in ps])
                slope = float(np.polyfit(x, y, 1)[0]) if np.ptp(x) > 1e-9 else None
                row = dict(regime=reg, fineness=fn, step=st, n=len(ps), med=float(np.median(le)), p90=float(np.quantile(le, 0.9)),
                           med_null=float(np.median(ln)), within=float(within), slope=slope)
                out["table"].append(row)
                print(f"| {reg} | {fn} | {st} | {len(ps)} | {row['med']:.4f} | {row['p90']:.4f} | {row['med_null']:.4f} | {within:.2f} | {'-' if slope is None else f'{slope:.2f}'} |")
    # by risk correlation, idle fine
    print()
    for corr in (0.0, 0.5, 0.9, 0.97):
        ps = [p for p in pairs if p["regime"] == "idle" and p["corr"] == corr and not p["coarse"]]
        if ps:
            print(f"- idle, corr {corr}: {len(ps)} pairs; predicted ratio range {min(p['pred'] for p in ps):.3f}-{max(p['pred'] for p in ps):.3f}; "
                  f"observed {min(p['obs'] for p in ps):.3f}-{max(p['obs'] for p in ps):.3f}; median |log err| {np.median([abs(np.log(p['obs'] / p['pred'])) for p in ps]):.4f}")
    # Deviation 1: the non-trivial subset (predicted ratio away from 1, i.e. corr > 0), prediction against the null
    print("\n| subset | pairs | median abs log err: prediction | null (ratio 1) | sign of log obs = sign of log pred (where |log obs| > resolution) | slope |")
    print("|---|---|---|---|---|---|")
    foc = []
    for corr in (0.5, 0.9, 0.97):
        for st in (0.1, 0.5):
            for reg in ("idle", "re-hedge"):
                ps = [p for p in pairs if p["corr"] == corr and p["step"] == st and p["regime"] == reg and not p["coarse"]]
                if reg == "idle":                              # Deviation 2: the idle regime's own coarse case is its fund-alone width
                    ps = [p for p in ps if abs(np.log(p["pred"])) > 0.01 and p["alone_frac"] < 0.9]
                if not ps:
                    continue
                lo = np.log([p["obs"] for p in ps]); lp = np.log([p["pred"] for p in ps])
                if reg == "idle":
                    lp_idle = lp
                else:
                    lp_idle = np.log([(lambda c0: 1.0)(None) for p in ps])
                mv = [(a, b) for a, b, p in zip(lo, lp, ps) if abs(a) > p["res"] * 2 and abs(b) > 0]
                sign = float(np.mean([np.sign(a) == np.sign(b) for a, b in mv])) if mv else None
                slope = float(np.polyfit(lp, lo, 1)[0]) if np.ptp(lp) > 1e-9 else None
                row = dict(corr=corr, step=st, regime=reg, n=len(ps), med_pred=float(np.median(np.abs(lo - lp))), med_null=float(np.median(np.abs(lo))),
                           sign=sign, slope=slope, moved=float(np.mean([abs(a) > p["res"] * 2 for a, p in zip(lo, ps)])))
                foc.append(row)
                print(f"| corr {corr}, step {st}, {reg} | {len(ps)} | {row['med_pred']:.4f} | {row['med_null']:.4f} | "
                      f"{'-' if sign is None else f'{sign:.2f}'} ({len(mv)}) | {'-' if slope is None else f'{slope:.2f}'} |"
                      + (f" share of widths moved beyond resolution: {row['moved']:.2f}" if reg == "re-hedge" else ""))
    ic = [p for p in pairs if p["regime"] == "idle" and p["corr"] > 0 and p["alone_frac"] >= 0.9]
    print(f"\n- idle pairs at the fund-alone width (width/alone >= 0.9; the idle regime's coarse case): {len(ic)}; "
          f"observed ratio within resolution of 1: {np.mean([abs(p['obs'] - 1) <= p['res'] * 2 for p in ic]):.2f}; corr {sorted(set(p['corr'] for p in ic))}")
    rh = [p for p in pairs if p["regime"] == "re-hedge" and p["corr"] > 0 and not p["coarse"]]
    mv = [p for p in rh if abs(np.log(p["obs"])) > p["res"] * 2]
    print(f"- re-hedge pairs (corr > 0, not coarse): {len(rh)}; moved beyond two grid steps {len(mv)} ({len(mv) / len(rh):.2f}); among them median |log ratio| "
          f"{np.median([abs(np.log(p['obs'])) for p in mv]):.3f}, 90th pct {np.quantile([abs(np.log(p['obs'])) for p in mv], 0.9):.3f}; "
          f"sign of log ratio = sign of r * Sigma_AE at {np.mean([np.sign(np.log(p['obs'])) == np.sign(p['r']) for p in mv]):.2f}")
    out["focused"] = foc
    json.dump(dict(out, pairs_sample=pairs[:2000]), open(HERE / "summary.json", "w"), separators=(",", ":"))
    import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    fig, ax = plt.subplots(figsize=(6, 5))
    for reg, col in (("idle", "C0"), ("re-hedge", "C3"), ("mixed", "0.6")):
        ps = [p for p in pairs if p["regime"] == reg and not p["coarse"]]
        ax.plot([p["pred"] for p in ps], [p["obs"] for p in ps], ".", color=col, ms=2, label=f"{reg} ({len(ps)})")
    lim = [0.6, 1.4]; ax.plot(lim, lim, "k--", lw=1); ax.set_xlim(lim); ax.set_ylim(lim)
    ax.set_xlabel("predicted width ratio (idle: cube root of v^idle ratio; else 1)"); ax.set_ylabel("observed width ratio w(r)/w(0)")
    ax.set_title("Experiment 038: r = +-0.8 against r = 0 (not coarse)"); ax.legend(fontsize=7)
    fig.tight_layout(); fig.savefig(HERE / "fig_ratio.png", dpi=130); plt.close(fig)


if __name__ == "__main__":
    main()
