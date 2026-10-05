"""Experiment 029 report and figures (uv run python experiments/029/report.py), from summary.json."""
import json
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
TOL = 1e-8


def stat_ok(r):
    return all(s == "optimal" for s in r["status"])


def main():
    S = json.load(open(HERE / "summary.json"))
    print("Tolerance: solvers' disagreement + 1e-8 (objective units; 1e-4 = 1 bp per quarter).\n")
    # curve 1
    c1 = S["c1"]; h = [r for r in c1 if r["hyp"]]
    print("## Curve 1 (part 2a, frictionless spanning ETFs)")
    print(f"- draws meeting 2a's hypotheses at the joint optimum (ETFs interior, budget slack): {len(h)} of {len(c1)}")
    print(f"- largest Lambda {max(r['Lam'] for r in h):.2e}, smallest {min(r['Lam'] for r in h):.2e}; largest Lambda_s {max(r['Lam_s'] for r in h):.2e}")
    print(f"- within tolerance: {sum(abs(r['Lam']) <= r['disagree'] + TOL and abs(r['Lam_s']) <= r['disagree'] + TOL for r in h)} of {len(h)}")
    x = [r for r in c1 if not r["hyp"]]
    if x:
        print(f"- outside the hypotheses ({len(x)}; an ETF at a bound or the budget binding): largest Lambda {max(r['Lam'] for r in x):.2e}, Lambda_s {max(r['Lam_s'] for r in x):.2e}")
    print(f"- largest solver disagreement {max(r['disagree'] for r in c1):.2e} (objective), {max(r['xdisagree'] for r in c1):.2e} (positions); non-optimal statuses {sum(not stat_ok(r) for r in c1)}\n")
    # curve 2
    c2 = S["c2"]
    edge = lambda r: abs(abs(r["m"]) - 0.001) < 1e-12        # Deviation 2: the two band-edge points per line
    print("## Curve 2 (part 2b, the corrected criterion); fund rate 10 bp")
    print("| ETF rate | Sigma_E | points (hypotheses hold, off the band edges) | criterion exact & Lambda <= tol | criterion inexact & Lambda > tol | disagreements | self-band holds but Lambda > tol | part-0 test agrees with criterion | Lambda zero inside the fund band | largest Lambda (bp) |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for re_, sg in ((0.0, 0.0), (0.001, 0.0), (0.005, 0.0), (0.01, 0.0), (0.005, 0.001)):
        rs = [r for r in c2 if r["rateE"] == re_ and r["sigE"] == sg]; hh = [r for r in rs if r["hyp"] and not edge(r)]
        zero = lambda r: r["Lam"] <= r["disagree"] + TOL
        crit = lambda r: r["self_band"] and r["fund_band"]
        a = sum(crit(r) and zero(r) for r in hh); b = sum((not crit(r)) and (not zero(r)) for r in hh)
        sbpos = sum(r["self_band"] and not zero(r) for r in hh)
        p0 = sum(r["part0"] == crit(r) for r in hh)
        inside = [r for r in hh if -0.001 <= r["m"] <= 0.001]
        print(f"| {re_ * 1e4:.0f} bp | {sg} | {len(rs)} ({len(hh)}) | {a} | {b} | {len(hh) - a - b} | {sbpos} | {p0}/{len(hh)} | {sum(zero(r) for r in inside)}/{len(inside)} | {max(r['Lam'] for r in rs) * 1e4:.3f} |")
    red = [r for r in c2 if r["rateE"] == 0.005 and abs(r["m"] - 0.003) < 1e-9 and r["sigE"] == 0][0]
    print(f"\nRed's point (fund marginal 30 bp, fund rate 10 bp, ETF rate 50 bp): Lambda = {red['Lam'] * 1e4:.3f} bp; self-band {red['self_band']}, fund band {red['fund_band']}; "
          f"stage 2 holds fund 1 at {red['x2_1']:.4f}, the joint optimum at {red['xJ_1']:.4f}")
    eds = [r for r in c2 if edge(r)]
    print(f"- band-edge points (fund marginal = +-10 bp exactly; {len(eds)}): largest Lambda {max(r['Lam'] for r in eds):.2e}; criterion exact at {sum(r['self_band'] and r['fund_band'] for r in eds)}")
    bad = [r for r in c2 if r["hyp"] and not edge(r) and ((r["self_band"] and r["fund_band"]) != (r["Lam"] <= r["disagree"] + TOL))]
    for r in bad[:10]:
        print(f"- disagreement: rate {r['rateE']}, m {r['m']}, Sigma_E {r['sigE']}: Lambda {r['Lam']:.3e}, self {r['self_band']}, fund {r['fund_band']}, part0 {r['part0']}")
    print(f"- b* = b_TB to {max(r['bstar_is_bTB'] for r in c2):.1e}; points outside the hypotheses {sum(not r['hyp'] for r in c2)}; largest solver disagreement {max(r['disagree'] for r in c2):.2e} (objective), {max(r['xdisagree'] for r in c2):.2e} (positions); non-optimal {sum(not stat_ok(r) for r in c2)}\n")
    # curve 3
    c3 = S["c3"]
    print("## Curve 3 (part 3a, the L_E bound)")
    for nm in ("equity-style", "fixed-income-style"):
        rs = [r for r in c3 if r["name"] == nm]; hh = [r for r in rs if r["hyp"]]
        rat = [r["Lam"] / r["bound"] for r in hh if r["bound"] > 0]
        print(f"- {nm}: {len(hh)} of {len(rs)} meet the hypotheses; largest Lambda {max(r['Lam'] for r in hh) * 1e4:.3f} bp; "
              f"largest Lambda / (L_E^2 / 2 gamma) = {max(rat):.2e}; Lambda <= L_E ||b_J - b*|| + tol at {sum(r['Lam'] <= r['bound2'] + r['disagree'] + TOL for r in hh)}/{len(hh)}; "
              f"violations of the first bound {sum(r['Lam'] > r['bound'] + r['disagree'] + TOL for r in hh)}")
        print("  | fee \\ ETF rate | " + " | ".join(f"{x * 1e4:.0f} bp" for x in (0, 0.0005, 0.001, 0.0025, 0.005, 0.01)) + " |")
        print("  |---|" + "---|" * 6)
        for f in (0, 0.00025, 0.0005, 0.001, 0.002, 0.003):
            row = [r for r in rs if r["fee"] == f]
            print(f"  | {f * 1e4:.1f} bp | " + " | ".join(f"{r['Lam'] * 1e4:.3f} / {r['bound'] * 1e4:.0f}" for r in sorted(row, key=lambda r: r['rateE'])) + " |")
    print("  (cells: Lambda / bound, bp)\n")
    # curve 4
    c4 = S["c4"]; hh = [r for r in c4 if r["hyp"]]
    print("## Curve 4 (parts 2c and 3b, one unreachable fund)")
    print(f"- points meeting the hypotheses (ETF interior and budget slack at both solutions): {len(hh)} of {len(c4)}; excluded by cap: "
          + ", ".join(f"cap {c}: {sum(1 for r in c4 if r['cap'] == c and not r['hyp'])}" for c in (0.25, 1.0)))
    print(f"- |solved Lambda - (psi(a_J) - psi(a*))|: max {max(abs(r['Lam'] - r['f_Lam']) for r in hh):.2e}; within tolerance {sum(abs(r['Lam'] - r['f_Lam']) <= r['disagree'] + TOL for r in hh)}/{len(hh)}")
    print(f"- |x_2 - a*|: max {max(abs(r['x2_1'] - r['f_astar']) for r in hh):.2e}; |x_J - a_J|: max {max(abs(r['xJ_1'] - r['f_aJ']) for r in hh):.2e}")
    print(f"- 3b bracket: lower <= Lambda at {sum(r['f_lower'] <= r['Lam'] + r['disagree'] + TOL for r in hh)}/{len(hh)}, Lambda <= upper at {sum(r['Lam'] <= r['f_upper'] + r['disagree'] + TOL for r in hh)}/{len(hh)}")
    print(f"- exact (a* = a_J) iff Lambda <= tol: {sum((abs(r['f_astar'] - r['f_aJ']) <= 1e-9) == (r['Lam'] <= r['disagree'] + TOL) for r in hh)}/{len(hh)}; largest Lambda {max(r['Lam'] for r in hh) * 1e4:.2f} bp")
    print(f"- a* on the grid: {sorted(set(round(r['f_astar'], 4) for r in c4))}; largest solver disagreement {max(r['disagree'] for r in c4):.2e} (objective), {max(r['xdisagree'] for r in c4):.2e} (positions); non-optimal {sum(not stat_ok(r) for r in c4)}\n")
    # curve 5
    c5 = S["c5"]
    print("## Curve 5 (soft procedure, claim 028 via claim 104 part 1)")
    inR = [r for r in c5 if r["bTB_in_R"]]; out = [r for r in c5 if not r["bTB_in_R"]]
    print(f"- b_TB inside R at {len(inR)} points: largest |Lambda_s| {max(abs(r['Lam_s']) for r in inR):.2e} (claim: 0)")
    ok = sum(-r['disagree'] - TOL <= r['Lam_s'] <= r['b1'] + r['disagree'] + TOL and r['b1'] <= r['b2'] + r['disagree'] + TOL for r in out)
    print(f"- b_TB outside R at {len(out)} points: 0 <= Lambda_s <= nu'(b_J - b_s) <= nu'(b* - b_s) holds at {ok}/{len(out)}; "
          f"largest Lambda_s {max(r['Lam_s'] for r in out) * 1e4:.3f} bp; largest ratio Lambda_s / nu'(b_J - b_s) {max(r['Lam_s'] / r['b1'] for r in out if r['b1'] > 0):.3f}")
    print(f"- first lambda_hat_1 with b_TB outside R: {min(r['l1'] for r in out) * 100:.2f}%; budget binding (eta > 1e-9) at {sum((r['eta'] or 0) > 1e-9 for r in c5)} points; "
          f"fibre-confined Lambda over the sweep: max {max(r['Lam'] for r in c5):.2e}")
    print(f"- largest solver disagreement {max(r['disagree'] for r in c5):.2e} (objective), {max(r['xdisagree'] for r in c5):.2e} (positions); non-optimal {sum(not stat_ok(r) for r in c5)}")
    print(f"\nseconds: {S['seconds']:.0f}")
    figures(S)


def figures(S):
    import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    fig, ax = plt.subplots(figsize=(6, 4))
    for re_, sg, st in ((0.0, 0.0, "-"), (0.001, 0.0, "-"), (0.005, 0.0, "-"), (0.01, 0.0, "-"), (0.005, 0.001, "--")):
        rs = sorted([r for r in S["c2"] if r["rateE"] == re_ and r["sigE"] == sg], key=lambda r: r["m"])
        ax.plot([r["m"] * 1e4 for r in rs], [r["Lam"] * 1e4 for r in rs], st, label=f"ETF rate {re_ * 1e4:.0f} bp" + (", Sigma_E (0.1%)^2" if sg else ""))
    ax.axvspan(-10, 10, color="0.9"); ax.set_xlabel("fund marginal alpha_hat_1 - gamma v_1 x^-_1 (bp)"); ax.set_ylabel("two-stage loss Lambda (bp)")
    ax.set_title("Curve 2: fund rate 10 bp (band shaded)"); ax.legend(fontsize=7); fig.tight_layout(); fig.savefig(HERE / "fig_curve2.png", dpi=130); plt.close(fig)
    fig, axes = plt.subplots(1, 2, figsize=(10, 4))
    for ax, xm in zip(axes, (0.0, 0.15)):
        for rt in (0.0, 0.002, 0.01):
            rs = sorted([r for r in S["c4"] if r["rate"] == rt and r["xm"] == xm and r["cap"] == 0.25], key=lambda r: r["a"])
            ax.plot([r["a"] * 100 for r in rs], [r["f_Lam"] * 1e4 for r in rs], label=f"formula, rate {rt * 1e4:.0f} bp")
            hh = [r for r in rs if r["hyp"]]
            ax.plot([r["a"] * 100 for r in hh][::8], [r["Lam"] * 1e4 for r in hh][::8], "k.", ms=3)
        ax.set_xlabel("alpha_hat (% per quarter)"); ax.set_ylabel("Lambda (bp)"); ax.set_title(f"Curve 4: unreachable fund, x^- = {xm}, cap 0.25")
    axes[0].legend(fontsize=7); fig.tight_layout(); fig.savefig(HERE / "fig_curve4.png", dpi=130); plt.close(fig)
    fig, ax = plt.subplots(figsize=(6, 4))
    rs = sorted(S["c5"], key=lambda r: r["l1"])
    ax.plot([r["l1"] * 100 for r in rs], [r["Lam_s"] * 1e4 for r in rs], label="Lambda_s (soft)")
    ax.plot([r["l1"] * 100 for r in rs], [r["b1"] * 1e4 for r in rs], "--", label="nu'(b_J - b_s)")
    ax.plot([r["l1"] * 100 for r in rs], [r["Lam"] * 1e4 for r in rs], ":", label="Lambda (fibre-confined)")
    ax.set_xlabel("lambda_hat_1 (% per quarter)"); ax.set_ylabel("bp"); ax.set_title("Curve 5: soft procedure and its bound"); ax.legend(fontsize=8)
    fig.tight_layout(); fig.savefig(HERE / "fig_curve5.png", dpi=130); plt.close(fig)


if __name__ == "__main__":
    main()
