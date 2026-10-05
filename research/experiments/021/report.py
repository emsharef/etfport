"""Experiment 021 report: tables from results.json (uv run python experiments/021/run.py report)."""
import json
import statistics
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent


def f(x, k=3):
    return "-" if x is None else f"{x:.{k}f}"


def width(e):
    return None if e is None else e[1] - e[0]


def main():
    R = json.load(open(HERE / "results.json"))
    print("## A. Quadratic costs: exact backward recursion (Riccati)\n")
    print(f"largest first-order-condition residual over all instances and quarters: {max(r['resid'] for r in R['riccati']):.1e}\n")
    print("| instance | gamma | T | trading speed at t=0 (funds; ETFs) | speed at t=T-1 | aim at t=0: funds | aim: ETFs | "
          "aim's alpha part (funds; ETFs) | value from 0 / incumbent (bp per quarter) |")
    print("|---|---|---|---|---|---|---|---|---|")
    for r in R["riccati"]:
        N = {"Q1": 1, "Q2": 2, "Q3": 3}[r["inst"]]
        p0, pl = r["per_t"][0], r["per_t"][-1]
        sp = lambda p: "; ".join(",".join(f"{v:.3f}" for v in xs) for xs in (p["speed"][:N], p["speed"][N:]))  # noqa: E731
        print(f"| {r['inst']} | {r['gamma']:.0f} | {r['T']} | {sp(p0)} | {sp(pl)} | {', '.join(f'{v:+.3f}' for v in p0['aim'][:N])} | "
              f"{', '.join(f'{v:+.3f}' for v in p0['aim'][N:])} | {', '.join(f'{v:+.3f}' for v in p0['aim_alpha'][:N])}; "
              f"{', '.join(f'{v:+.3f}' for v in p0['aim_alpha'][N:])} | {r['V0_zero']:.2f} / {r['V0_incumbent']:.2f} |")
    print("\n## B. Q1 grid cross-check (quadratic costs; grid DP against the exact recursion, interior of the box)\n")
    print("| gamma | T | h | box (fund; ETF) | max value difference (bp per quarter) | max policy difference (holdings) |")
    print("|---|---|---|---|---|---|")
    for r in R["q1_grid"]:
        print(f"| {r['gamma']:.0f} | {r['T']} | 1/{round(1 / r['h'])} | [{r['box'][0][0]:.2f}, {r['box'][0][1]:.2f}]; [{r['box'][1][0]:.2f}, {r['box'][1][1]:.2f}] | {r['max_value_diff_bp_q']:.4f} | {r['max_policy_diff']:.4f} |")

    P = R["prop"]
    base = [r for r in P if r["inst"] == "P1" and r["kappa_fund"] == 0.01 and r["kappa_etf"] == 0.0005]

    def key(b):
        return (b["t"], b["m_index"])

    print("\n## C. P1 (proportional costs 100 bp fund / 5 bp ETF, long-only caps): no-trade band per instrument\n")
    print("Each instrument's band is read at belief points where its own frictionless target lies strictly inside [0, 1] (Deviation 2). Width in holdings "
          "(fraction of wealth). Resolved: width changes by < 10% from h = 1/100 to 1/200.\n")
    print("| gamma | T | points (t, m) | fund width median [min, max] at h=1/200 | ETF width median [min, max] | "
          "resolved fund / ETF | fund edge at a cap (points) |")
    print("|---|---|---|---|---|---|---|")
    summary = {}
    for g in (2.0, 5.0, 10.0):
        for T in (4, 8):
            rr = {r["h"]: r for r in base if r["gamma"] == g and r["T"] == T}
            b200 = {key(b): b for b in rr[1 / 200]["bands"]}
            b100 = {key(b): b for b in rr[1 / 100]["bands"]}
            fw, ew, fres, eres, capf = [], [], 0, 0, 0
            for k, b in b200.items():
                wf, we = width(b["edges"][0]), width(b["edges"][1])
                if wf is not None:
                    fw.append(wf); capf += b["edges"][0][2] or b["edges"][0][3]
                if we is not None:
                    ew.append(we)
                if k in b100:
                    o = b100[k]
                    if wf and width(o["edges"][0]) is not None and abs(width(o["edges"][0]) - wf) < 0.1 * wf:
                        fres += 1
                    if we and width(o["edges"][1]) is not None and abs(width(o["edges"][1]) - we) < 0.1 * we:
                        eres += 1
            summary[(g, T)] = (fw, ew)
            if fw:
                print(f"| {g:.0f} | {T} | {len(b200)} | {statistics.median(fw):.3f} [{min(fw):.3f}, {max(fw):.3f}] | "
                      f"{statistics.median(ew):.3f} [{min(ew):.3f}, {max(ew):.3f}] | {fres} / {eres} of {len(b200)} | {capf} |")
            else:
                print(f"| {g:.0f} | {T} | 0 | - | - | - | - |")
    print("\n**Band width against belief volatility (P1, gamma 5, T 8, h = 1/200; medians over belief points by quarter):**\n")
    r = next(r for r in base if r["gamma"] == 5.0 and r["T"] == 8 and r["h"] == 1 / 200)
    print("| quarter t | innovation sd of the alpha mean (bp) | fund width | ETF width | points |")
    print("|---|---|---|---|---|")
    for t in range(8):
        bs = [b for b in r["bands"] if b["t"] == t]
        fw = [width(b["edges"][0]) for b in bs if b["edges"][0]]
        ew = [width(b["edges"][1]) for b in bs if b["edges"][1]]
        print(f"| {t} | {r['innov_sd'][t] * 1e4:.2f} | {f(statistics.median(fw)) if fw else '-'} | "
              f"{f(statistics.median(ew)) if ew else '-'} | {len(bs)} |")
    print("\n## D. Cost sweep (P1, gamma 5, T 4, t = 0; common kappa for both instruments)\n")
    print("| kappa (bp) | h | fund width median | ETF width median | points |")
    print("|---|---|---|---|---|")
    sweep = {}
    for r in P:
        if r["inst"] == "P1" and r["gamma"] == 5.0 and r["T"] == 4 and r["kappa_fund"] == r["kappa_etf"]:
            bs = [b for b in r["bands"] if b["t"] == 0]
            fw = [width(b["edges"][0]) for b in bs if b["edges"][0]]
            ew = [width(b["edges"][1]) for b in bs if b["edges"][1]]
            fm, em = (statistics.median(fw) if fw else None), (statistics.median(ew) if ew else None)
            sweep[(r["kappa_fund"], r["h"])] = (fm, em)
            print(f"| {r['kappa_fund'] * 1e4:.0f} | 1/{round(1 / r['h'])} | {f(fm)} | {f(em)} | {len(bs)} |")
    ks = sorted({k for k, h in sweep})
    for lab, i in (("fund", 0), ("ETF", 1)):
        pts = [(k, sweep[(k, 1 / 200)][i]) for k in ks if sweep.get((k, 1 / 200), (None, None))[i]]
        if len(pts) >= 2:
            sl = np.polyfit(np.log([p[0] for p in pts]), np.log([p[1] for p in pts]), 1)[0]
            print(f"- {lab}: log-log slope of median width on kappa at h = 1/200: {sl:.3f} (leading-order small-cost theory: 1/3)")
    print("\n## E. P2 (two funds, one ETF; coarse 4-D grid)\n")
    print("| gamma | T | h | points | fund 1 width median | fund 2 width median | ETF width median |")
    print("|---|---|---|---|---|---|---|")
    for r in P:
        if r["inst"] == "P2":
            bs = r["bands"]
            med = lambda i: statistics.median([width(b["edges"][i]) for b in bs if b["edges"][i]]) if any(b["edges"][i] for b in bs) else None  # noqa: E731
            print(f"| {r['gamma']:.0f} | {r['T']} | 1/{round(1 / r['h'])} | {len(bs)} | {f(med(0))} | {f(med(1))} | {f(med(2))} |")
    print("\n## F. Values from the grid DP (bp per quarter, at the prior mean)\n")
    print("| instance | gamma | T | h | kappa fund/ETF (bp) | from 0 | from incumbent |")
    print("|---|---|---|---|---|---|---|")
    for r in P:
        if r["h"] in (1 / 200, 1 / 40):
            print(f"| {r['inst']} | {r['gamma']:.0f} | {r['T']} | 1/{round(1 / r['h'])} | {r['kappa_fund'] * 1e4:.0f}/{r['kappa_etf'] * 1e4:.0f} | "
                  f"{r['V0_zero']:.2f} | {r['V0_incumbent']:.2f} |")


if __name__ == "__main__":
    main()
