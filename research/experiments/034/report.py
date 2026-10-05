"""Experiment 034 report and figures (uv run python experiments/034/report.py), from summary.json."""
import json
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent


def main():
    S = json.load(open(HERE / "summary.json"))
    C1 = S["c1"]
    base = [c for c in C1 if c["PLs"] == 1.0 and tuple(c["lam"]) == (0.015, 0.005)]
    for c in C1:                                                     # the strip with the box (part 3's clip; part 5(b))
        kp, km = c["rates"]
        for r in c["rows"]:
            m = r["a"] - 5 * (0.02 ** 2 + 0.0035 ** 2) * c["xm1"]
            r["pred"] = "buy" if (m > kp and c["xm1"] < 0.25) else ("sell" if (m < -km and c["xm1"] > 0) else "hold")
            r["dxc"] = r["dx"] if all(st == "optimal" for st in r["status"]) else 0.0
    rows = [r for c in base for r in c["rows"]]; hh = [r for r in rows if r["hyp"] and not r["edge"]]
    print("## Curve 1 (part 3: the hold strip, frictionless spanning ETFs)")
    print(f"- {len(rows)} points; {sum(not r['hyp'] for r in rows)} outside the hypotheses; {sum(r['edge'] for r in rows)} on a strip edge")
    print(f"- classification = strip: {sum(r['dec'] == r['pred'] for r in hh)}/{len(hh)}; decisions {dict(Counter(r['dec'] for r in hh))}")
    print(f"- holding against the clip: largest |difference| {max(abs(r['x1'] - r['clip']) for r in hh):.1e} (solver holding disagreement where both optimal {max(r['dxc'] for r in rows):.1e}; OSQP at its iteration cap at {sum(r['status'][1] != 'optimal' for c in C1 for r in c['rows'])} points, CLARABEL alone there)")
    print(f"- ETF holdings against R'(y* - B^A' x^A): largest |difference| {max(r['etf_err'] for r in hh):.1e}")
    print(f"- part 1's multiplier criterion holds at the solved optimum: {sum(r['p1'] for r in rows)}/{len(rows)}")
    by = defaultdict(list)
    for c in C1:
        for r in c["rows"]:
            if r["hyp"]:
                by[(tuple(c["rates"]), c["xm1"], r["a"])].append(r["x1"])
    spread = [max(v) - min(v) for v in by.values() if len(v) > 1]
    print(f"- premium independence (5 premium vectors x 3 P^lambda scales): largest change of fund 1's holding {max(spread):.1e} over {len(spread)} (alpha, incumbent, rates) points\n")
    C2 = [r for r in S["c2"] if r["ok"]]; hh = [r for r in C2 if r["hyp"]]
    print("## Curve 2 (part 4: the ETF-friction bracket)")
    print(f"- {len(hh)} of {len(S['c2'])} threshold cells meet the hypotheses")
    inb = [r for r in hh if r["lo"] - 1e-7 <= r["A"] <= r["hi"] + 1e-7]      # Deviation 2: threshold precision 1e-7
    print(f"- empirical purchase threshold in A_1 inside [kappa^+ - h^-, kappa^+ + h^+]: {len(inb)}/{len(hh)}")
    tr = [r for r in hh if r["exp_pos"] is not None and r["pos"] is not None]
    print(f"- ETFs all trading at the onset: {len(tr)} cells; position against the one implied by the ETFs' trade signs (sold share of |r|): largest |difference| {max(abs(r['pos'] - r['exp_pos']) for r in tr):.1e}; "
          f"positions {sorted(set(round(r['pos'], 3) for r in tr))}" if tr else "- no cells with every ETF trading")
    re = [r for r in hh if r["rehedge"] and r["pos"] is not None]; op = [r for r in hh if r["opposite"] and r["pos"] is not None]
    idle = [r for r in hh if not r["rehedge"] and not r["opposite"] and r["pos"] is not None]
    print(f"- ETFs re-hedge the purchase: {len(re)} cells, position in the bracket {min(r['pos'] for r in re):.4f}-{max(r['pos'] for r in re):.4f} (claim: 1)" if re else "- no re-hedging cells")
    print(f"- ETFs traded the other way: {len(op)} cells, position {min(r['pos'] for r in op):.4f}-{max(r['pos'] for r in op):.4f} (the lower end is 0)" if op else "- no opposite-direction cells")
    print(f"- ETFs idle (or mixed): {len(idle)} cells, position {min(r['pos'] for r in idle):.3f}-{max(r['pos'] for r in idle):.3f}" if idle else "")
    z = [r for r in hh if r["pos"] is None]
    print(f"- zero ETF rate ({len(z)} cells): |A - kappa^+| max {max(abs(r['A'] - r['lo']) for r in z):.1e} (the bracket is a point)")
    su = [c for d in S["c2_suff"] if d["hyp"] for c in d["cases"]]
    print(f"- sufficient conditions at the incumbent (500 draws; {sum(d['hyp'] for d in S['c2_suff'])} meet the hypotheses): {len(su)} cases, "
          f"violations {sum(not ok for _, ok in su)} ({dict(Counter(k for k, _ in su))})\n")
    print("## Curve 3 (part 5(a): binding budget)")
    print("| point | ETF rate | h | side | eta | observed threshold (alpha - gamma v x^-) | literal eta +- (1+eta) kappa | corrected eta (1 - sum r) +- (1+eta) kappa | A - eta(1 - sum r) in the (1+eta)-scaled bracket |")
    print("|---|---|---|---|---|---|---|---|---|")
    lit_ok = cor_ok = br_ok = n = 0
    for r in S["c3"]:
        for side in ("1", "-1"):
            d = r.get(f"side{side}")
            if not d or not d["hyp"] or d["eta"] < 1e-9:
                continue
            n += 1
            lit = abs(d["m"] - d["literal"]) < 1e-6; cor = abs(d["m"] - d["corrected"]) < 1e-6          # Deviation 2: 1e-6 under a binding budget
            inb = d["br"][0] - 1e-6 <= d["A_adj"] <= d["br"][1] + 1e-6
            lit_ok += lit; cor_ok += cor; br_ok += inb
            print(f"| {r['name']} | {r['rE'] * 1e4:.0f} bp | {r['h']} | {'buy' if side == '1' else 'sell'} | {d['eta']:.2e} | {d['m'] * 1e4:.3f} bp | {d['literal'] * 1e4:.3f} bp | {d['corrected'] * 1e4:.3f} bp | {inb} |")
    print(f"- 25 bp ETF rate: binding cases meeting the hypotheses {sum(1 for r in S['c3'] if r['rE'] > 0 for k in ('side1', 'side-1') if r.get(k) and r[k]['hyp'] and r[k]['eta'] > 1e-9)} (ETFs start at zero and stay there)")
    print(f"\n- binding cases: {n}; observed = literal: {lit_ok}; observed = corrected (to 1e-6; largest gap {max(abs(r[k]["m"] - r[k]["corrected"]) for r in S["c3"] for k in ("side1", "side-1") if r.get(k) and r[k]["hyp"] and r[k]["eta"] > 1e-9):.1e}): {cor_ok}; inside the scaled bracket: {br_ok}\n")
    C4 = S["c4"]
    print("## Curve 4 (parts 1 and 2 on 300 random draws, ETFs at bounds included)")
    print(f"- part 1's criterion at the solved optimum: {sum(r['p1'] for r in C4)}/{len(C4)}; draws with an ETF at a bound {sum(r['etf_bound'] for r in C4)}; binding budget {sum(r['eta'] > 1e-9 for r in C4)}")
    ok2 = [r for r in C4 if r["part2"] is not None]
    print(f"- part 2's test: verdict available at {len(ok2)}; 'no fund traded' verdict = full solve at {sum(r['part2'] == (not r['traded']) for r in ok2)}/{len(ok2)}; "
          f"verdicts {dict(Counter((r['part2'], r['traded']) for r in ok2))}\n")
    print("## Curve 5 (part 6: several reviews, exact DP)")
    C5 = [c for c in S["c5"] if c["hfac"] == 1]
    thr = [(c, r) for c in C5 for r in c["rows"] if r["thr"] is not None]
    inb = sum(r["lo"] - r["c"] * r["hx"] <= r["thr"] <= r["hi"] + r["c"] * r["hx"] for c, r in thr)
    print(f"- purchase threshold from zero inside [(1 - beta) kappa^+, kappa^+ + beta kappa^-] (+- one grid step c h): {inb}/{len(thr)}")
    pos = [(r["thr"] - r["lo"]) / (r["hi"] - r["lo"]) for c, r in thr]
    print(f"- its position in the bracket: {min(pos):.3f} to {max(pos):.3f} (median {np.median(pos):.3f}); thresholds in units of kappa: "
          f"{min(r['thr'] / c['kap'] for c, r in thr):.3f} to {max(r['thr'] / c['kap'] for c, r in thr):.3f}")
    ex = [(c, r) for c in C5 for r in c["rows"] if r["excess"] is not None]
    print(f"- band inside the one-review band (interior belief rows): largest excess {max(r['excess'] / r['hx'] for c, r in ex):.2f} grid steps")
    last = [(c, r) for c in C5 for r in c["rows"] if r["t"] == c["T"] - 1 and r["eq"] is not None]
    print(f"- equality at the last review: largest edge difference {max(r['eq'] / r['hx'] for c, r in last):.2f} grid steps")
    wr = [r["width_ratio"] for c in C5 for r in c["rows"] if r["width_ratio"] is not None and r["t"] < c["T"] - 1]
    print(f"- width / one-review width before the last review: {min(wr):.3f} to {max(wr):.3f}")
    for c in [c for c in S["c5"] if c["hfac"] == 2]:
        c1 = [x for x in S["c5"] if x["hfac"] == 1 and x["beta"] == c["beta"] and x["T"] == c["T"] and x["kap"] == c["kap"] and x["pr"] == c["pr"]][0]
        d = max(abs(a["thr"] - b["thr"]) for a, b in zip(c["rows"], c1["rows"]) if a["thr"] is not None and b["thr"] is not None)
        print(f"- resolution check (beta {c['beta']}, T {c['T']}, kappa {c['kap']}, p0 {c['pr']}): threshold change at h/2 {d:.1e} ({d / c['kap']:.4f} kappa)")
    print(f"\nseconds: {S['seconds']:.0f}")
    figures(S)


def figures(S):
    import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    fig, axes = plt.subplots(1, 3, figsize=(15, 4))
    ax = axes[0]
    col = {"buy": "C3", "sell": "C0", "hold": "0.7"}
    for c in S["c1"]:
        if c["PLs"] == 1.0 and tuple(c["lam"]) == (0.015, 0.005) and tuple(c["rates"]) == (0.005, 0.001):
            for r in c["rows"]:
                if r["hyp"]:
                    ax.plot(r["a"] * 100, c["xm1"], "s", color=col[r["dec"]], ms=2)
    x = np.linspace(0, 0.25, 50); gv = 5 * (0.02 ** 2 + 0.0035 ** 2)
    ax.plot((gv * x + 0.005) * 100, x, "k-", lw=1); ax.plot((gv * x - 0.001) * 100, x, "k-", lw=1)
    ax.set_xlabel("alpha_hat_1 (%)"); ax.set_ylabel("x^-_1"); ax.set_title("Curve 1: buy (red) / hold / sell (blue); strip edges, rates 50/10 bp")
    ax = axes[1]
    for xm, l1, mk in ((0.1, 0.005, "o"), (0.1, 0.015, "s"), (0.1, 0.03, "^")):
        rs = sorted([r for r in S["c2"] if r["ok"] and r["hyp"] and r["xm1"] == xm and r["l1"] == l1 and r["fee"] == 0], key=lambda r: r["rE"])
        ax.plot([r["rE"] * 1e4 for r in rs], [r["A"] * 1e4 for r in rs], mk + "-", ms=4, label=f"lambda_1 = {l1 * 100}%")
    rE = np.array([0, 5, 10, 25, 50, 100]); hsum = 1.5
    ax.plot(rE, 20 + hsum * rE, "k--", lw=1); ax.plot(rE, 20 - hsum * rE, "k--", lw=1)
    ax.set_xlabel("ETF rate (bp)"); ax.set_ylabel("purchase threshold in A_1 (bp)"); ax.set_title("Curve 2: threshold and bracket (fund 20 bp)"); ax.legend(fontsize=7)
    ax = axes[2]
    for c in S["c5"]:
        if c["hfac"] == 1 and c["T"] == 20 and c["pr"] == 0.3 and c["kap"] == 0.001:
            ax.plot([r["t"] for r in c["rows"]], [r["thr"] / c["kap"] if r["thr"] else np.nan for r in c["rows"]], label=f"beta {c['beta']}")
            ax.axhline(1 - c["beta"], ls=":", lw=0.8); ax.axhline(1 + c["beta"], ls=":", lw=0.8)
    ax.set_xlabel("review t"); ax.set_ylabel("threshold / kappa"); ax.set_title("Curve 5: purchase threshold from zero (T = 20, kappa 10 bp)"); ax.legend(fontsize=7)
    fig.tight_layout(); fig.savefig(HERE / "fig_curves.png", dpi=130); plt.close(fig)


if __name__ == "__main__":
    main()
