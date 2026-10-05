"""Experiment 036 report and figures (uv run python experiments/036/report.py), from summary.json."""
import json
from collections import Counter
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent


def good(b):
    return b["interior"] and b["contig"]


def main():
    S = json.load(open(HERE / "summary.json"))
    C = [c for c in S["cells"] if c["hfac"] == 1]
    rows = [(c, r) for c in C for r in c["rows"]]
    bands = [(c, r, b) for c, r in rows for b in r["bands"] if good(b)]
    print(f"{len(C)} DP cells x 8 reviews; {len(bands)} (cell, review, ETF incumbent) fund bands off the grid edges; "
          f"non-contiguous bands {sum(1 for c, r in rows for b in r['bands'] if b['interior'] and not b['contig'])}\n")
    print("## Part 1b: the residual-variance ceiling")
    over = [(c, r, b) for c, r, b in bands if (b["hi"] - b["lo"]) > r["ceil"] + c["hA"]]
    print(f"- width <= (kappa^+_A + kappa^-_A)/(gamma sigma^2_A.E) + one grid step: {len(bands) - len(over)}/{len(bands)}; "
          f"largest width/ceiling {max((b['hi'] - b['lo']) / r['ceil'] for c, r, b in bands):.4f}")
    for corr in (0.0, 0.5, 0.9, 0.97):
        w = [(b["hi"] - b["lo"]) / r["ceil"] for c, r, b in bands if c["corr"] == corr]
        c0 = [c for c in C if c["corr"] == corr][0]
        print(f"  - corr {corr}: width/ceiling {min(w):.3f}-{max(w):.3f}; ceiling / fund-alone width = 1/(1 - corr^2) = {1 / (1 - corr ** 2):.2f}")
    print()
    print("## Part 1c: the bracket")
    vh = sum(b["hi"] > r["hi_b"] + c["hA"] for c, r, b in bands); vl = sum(b["lo"] < r["lo_b"] - c["hA"] for c, r, b in bands)
    print(f"- hi <= a* + [kappa^-_A + beta kappa^+_A + H^+]/c^res: violations {vh}; lo >= a* - [kappa^+_A + beta kappa^-_A + H^-]/c^res: violations {vl} (of {len(bands)})")
    print(f"- largest hi / bracket {max(b['hi'] / r['hi_b'] for c, r, b in bands if r['hi_b'] > 0):.3f}; largest lo / bracket {max(b['lo'] / r['lo_b'] for c, r, b in bands if r['lo_b'] < 0):.3f}\n")
    print("## Part 1d: the last review")
    last = [(c, r, b) for c, r, b in bands if r["t"] == 7]
    reg = Counter(); miss = []
    for c, r, b in last:
        dh, dl = b["dir_hi"], b["dir_lo"]
        kind = "idle both" if dh == 0 and dl == 0 else ("same slope" if dh == dl else ("opposite" if dh * dl == -1 else "mixed"))
        reg[kind] += 1
        for k in ("hi", "lo"):
            f = b.get(f"f_{k}")
            if f is not None and abs(b[k] - f) > c["hA"]:
                miss.append((c, b, k, f))
        w = b["hi"] - b["lo"]
        if kind == "same slope" and abs(w - r["ceil"]) > 2 * c["hA"]:
            miss.append((c, b, "width-same", r["ceil"]))
        if kind == "opposite":
            wo = r["ceil"] - abs(c["rho"]) * (c["kE"][0] + c["kE"][1]) / c["cres"]
            if abs(w - wo) > 2 * c["hA"]:
                miss.append((c, b, "width-opposite", wo))
        if kind == "idle both" and abs(w - r["alone"]) > 2 * c["hA"]:
            miss.append((c, b, "width-idle", r["alone"]))
    print(f"- regimes at the last review: {dict(reg)}")
    print(f"- edges against 1d's formulas (where the ETF trades at the edge) and widths by regime: mismatches beyond one or two grid steps {len(miss)} of {len(last)}")
    for c, b, k, f in miss[:6]:
        print(f"  - corr {c['corr']} kA {c['kA']} kE {c['kE']}: {k} observed {(b['hi'] - b['lo']) if 'width' in k else b[k]:.5f} vs {f:.5f} (hA {c['hA']:.1e}; dirs {b['dir_lo']}, {b['dir_hi']})")
    wl = [((b["hi"] - b["lo"]) - r["alone"]) / (r["ceil"] - r["alone"]) for c, r, b in last if r["ceil"] > r["alone"] + 1e-12]
    print(f"- last-review width between the fund-alone width (0) and the ceiling (1): {min(wl):.3f} to {max(wl):.3f}; "
          f"largest shortfall below the fund-alone width {max((r['alone'] - (b['hi'] - b['lo'])) / c['hA'] for c, r, b in last):.2f} grid steps")
    for hf in (2, 4):
        for d in [c for c in S["cells"] if c["hfac"] == hf and c["kA"] == [0.01, 0.0]]:
            r = d["rows"][-1]; bs = [b for b in r["bands"] if good(b)]
            e = [abs(b["hi"] - b["f_hi"]) / d["hA"] for b in bs if b.get("f_hi") is not None]
            print(f"  - asymmetric cell at h/{hf}: largest |hi - 1d formula| {max(e) if e else float('nan'):.2f} fine grid steps = {max(e) * d['hA'] if e else float('nan'):.4f}")
    cv = S["convex"]; diffs = []
    for d in cv:
        cell = [c for c in C if c["corr"] == d["corr"] and c["kA"] == d["kA"] and c["kE"] == d["kE"] and c["r"] == 0.0 and c["step"] == 0.5][0]
        bl = {round(b["dE"], 12): b for b in cell["rows"][-1]["bands"]}
        for x in d["rows"]:
            b = bl.get(round(x["dE"], 12))
            if b and good(b) and x.get("seed_held") and x["hi"] is not None and x["lo"] is not None:
                SAE = cell["rho"] * 0.0854 ** 2
                eff = cell["hA"] + abs(SAE) * 5.0 * cell["hE"] / cell["cres"]          # Deviation 2: the ETF step's reach into the fund edge
                diffs.append((max(abs(b["hi"] - x["hi"]), abs(b["lo"] - x["lo"])) / cell["hA"], max(abs(b["hi"] - x["hi"]), abs(b["lo"] - x["lo"])) / eff))
    print(f"- convex program (grid-free) against the DP at the last review: {len(diffs)} incumbents, largest edge difference {max(d[0] for d in diffs):.2f} fund grid steps, "
          f"{max(d[1] for d in diffs):.2f} effective resolutions (h_A + |Sigma_AE| gamma h_E / c^res)\n")
    print("## Part 2: the outer parallelotope")
    print(f"- no-trade points outside x* + (gamma Sigma)^-1 prod[...] (beyond one grid step): {sum(r['outside'] for c, r in rows)} of {sum(r['nt_points'] for c, r in rows)}")
    dm = [r["diam"] for c, r in rows if r["diam"] is not None]
    print(f"- Sigma-diameter: largest (lhs - rhs - grid slack)/rhs over sampled pairs {max(dm):.2e} (<= 0 means the inequality holds)")
    fa = [(r["extA"][1] - r["extA"][0]) / (r["parA"][1] - r["parA"][0]) for c, r in rows if r["extA"]]
    fe = [(r["extE"][1] - r["extE"][0]) / (r["parE"][1] - r["parE"][0]) for c, r in rows if r["extE"]]
    print(f"- the region's extent / the parallelotope's, fund axis {min(fa):.2f}-{max(fa):.2f}, ETF axis {min(fe):.2f}-{max(fe):.2f}\n")
    print("## Part 3: frictionless ETF")
    fr = [(c, r) for c, r in rows if c["kE"] == [0.0, 0.0]]
    dif = []; spread = []
    for c, r in fr:
        bs = [b for b in r["bands"] if good(b)]
        if not bs or r["reduced"] is None:
            continue
        dif.append(max(max(abs(b["lo"] - r["reduced"][0]), abs(b["hi"] - r["reduced"][1])) for b in bs) / c["hA"])
        spread.append(max(max(b["hi"] for b in bs) - min(b["hi"] for b in bs), max(b["lo"] for b in bs) - min(b["lo"] for b in bs)) / c["hA"])
    print(f"- fund band against the reduced one-instrument DP band: largest edge difference {max(dif):.2f} grid steps ({len(dif)} (cell, review))")
    print(f"- dependence on the ETF incumbent: largest edge range across incumbents {max(spread):.2f} grid steps\n")
    print("## Open item: the targets' innovation correlation r (t = 0, T = 8, ETF 10 bp)")
    print("| risk corr | fund rate | step | r = -0.8 | r = 0 | r = +0.8 | (median width/ceiling; centre (lo+hi)/2 / ceiling, median) |")
    print("|---|---|---|---|---|---|---|")
    for corr in (0.97, 0.5):
        for kA in ([0.001, 0.001], [0.005, 0.005]):
            for st in (0.5, 0.1):
                cells = []
                for r_ in (-0.8, 0.0, 0.8):
                    c = [x for x in C if x["corr"] == corr and x["kA"] == kA and x["kE"] == [0.001, 0.001] and x["r"] == r_ and x["step"] == st][0]
                    bs = [b for b in c["rows"][0]["bands"] if good(b)]
                    w = np.median([(b["hi"] - b["lo"]) / c["rows"][0]["ceil"] for b in bs]); m = np.median([(b["hi"] + b["lo"]) / 2 / c["rows"][0]["ceil"] for b in bs])
                    cells.append(f"{w:.3f}; {m:+.3f}")
                print(f"| {corr} | {kA[0] * 1e4:.0f} bp | {st} | " + " | ".join(cells) + " | |")
    print()
    for d in [c for c in S["cells"] if c["hfac"] == 2 and c["kA"] != [0.01, 0.0]]:
        base = [c for c in C if c["corr"] == d["corr"] and c["kA"] == d["kA"] and c["kE"] == d["kE"] and c["r"] == d["r"] and c["step"] == d["step"]][0]
        w2 = np.median([(b["hi"] - b["lo"]) for b in d["rows"][0]["bands"] if good(b)]); w1 = np.median([(b["hi"] - b["lo"]) for b in base["rows"][0]["bands"] if good(b)])
        print(f"- resolution check (corr {d['corr']}, kA {d['kA'][0]}, kE {d['kE'][0]}, r {d['r']}, step {d['step']}): median width at h/2 {w2:.5f} vs h {w1:.5f} ({abs(w2 - w1) / base['hA']:.2f} coarse steps)")
    print(f"\nseconds: {S['seconds']:.0f}")
    figures(S)


def figures(S):
    import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    C = [c for c in S["cells"] if c["hfac"] == 1]
    fig, axes = plt.subplots(1, 3, figsize=(15, 4))
    ax = axes[0]
    for kA, mk in (([0.001, 0.001], "o"), ([0.005, 0.005], "s")):
        xs, ys = [], []
        for corr in (0.0, 0.5, 0.9, 0.97):
            c = [x for x in C if x["corr"] == corr and x["kA"] == kA and x["kE"] == [0.001, 0.001] and x["r"] == 0.0 and x["step"] == 0.5][0]
            bs = [b for b in c["rows"][0]["bands"] if good(b)]
            xs.append(corr); ys.append(np.median([(b["hi"] - b["lo"]) for b in bs]) / c["rows"][0]["alone"])
        ax.plot(xs, ys, mk + "-", label=f"fund {kA[0] * 1e4:.0f} bp")
    cc = np.linspace(0, 0.97, 50); ax.plot(cc, 1 / (1 - cc ** 2), "k--", lw=1, label="ceiling / fund-alone = 1/(1 - corr^2)")
    ax.set_yscale("log"); ax.set_xlabel("risk correlation"); ax.set_ylabel("band width / fund-alone width"); ax.set_title("Width against corr (ETF 10 bp, t = 0, T = 8)"); ax.legend(fontsize=7)
    ax = axes[1]
    for corr, mk in ((0.97, "o"), (0.5, "s")):
        xs, lo_, md, hi_ = [], [], [], []
        for kE in ([0.0, 0.0], [0.0002, 0.0002], [0.001, 0.001], [0.005, 0.005]):
            c = [x for x in C if x["corr"] == corr and x["kA"] == [0.001, 0.001] and x["kE"] == kE and x["r"] == 0.0 and x["step"] == 0.5][0]
            r = c["rows"][-1]; w = [((b["hi"] - b["lo"]) - r["alone"]) / (r["ceil"] - r["alone"]) for b in r["bands"] if good(b)]
            xs.append(kE[0] * 1e4 + 0.1); lo_.append(min(w)); md.append(np.median(w)); hi_.append(max(w))
        ax.plot(xs, md, mk + "-", label=f"corr {corr} (median; bars min-max)")
        ax.vlines(xs, lo_, hi_)
    ax.set_xscale("log"); ax.set_xlabel("ETF rate (bp)"); ax.set_ylabel("(width - fund-alone) / (ceiling - fund-alone)"); ax.set_title("Last review: width between the two regimes"); ax.legend(fontsize=7)
    ax = axes[2]
    for st, ls in ((0.5, "-"), (0.1, "--")):
        for corr, col in ((0.97, "C0"), (0.5, "C1")):
            ys = []
            for r_ in (-0.8, 0.0, 0.8):
                c = [x for x in C if x["corr"] == corr and x["kA"] == [0.001, 0.001] and x["kE"] == [0.001, 0.001] and x["r"] == r_ and x["step"] == st][0]
                ys.append(np.median([(b["hi"] - b["lo"]) / c["rows"][0]["ceil"] for b in c["rows"][0]["bands"] if good(b)]))
            ax.plot([-0.8, 0, 0.8], ys, ls, color=col, marker="o", ms=3, label=f"corr {corr}, step {st}")
    ax.set_xlabel("innovation correlation r"); ax.set_ylabel("width / ceiling (t = 0)"); ax.set_title("Open item: width against r (fund 10 bp, ETF 10 bp)"); ax.legend(fontsize=7)
    fig.tight_layout(); fig.savefig(HERE / "fig_bands.png", dpi=130); plt.close(fig)


if __name__ == "__main__":
    main()
