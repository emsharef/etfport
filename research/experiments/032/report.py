"""Experiment 032 report and figures (uv run python experiments/032/report.py), from summary.json."""
import json
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
TOL = 1e-8
ZERO = 1e-11      # Deviation 3: zero tests at the objective resolution (both solvers optimal: disagreement <= 1.2e-11)


def dis(r):
    """The solvers' disagreement where both returned optimal; CLARABEL alone otherwise (Deviation 3)."""
    return r["dis"] if all(s == "optimal" for s in r["status"]) else 0.0


def ok(r, a, b):
    return abs(r[a] - r[b]) <= dis(r) + TOL


def main():
    S = json.load(open(HERE / "summary.json"))
    print("Tolerance: solvers' disagreement + 1e-8 (objective units; 1e-4 = 1 bp per quarter).\n")
    sp = S["spanning"]
    names = {1: "Curve 1 (C^- against net alpha)", 2: "Curve 2 (C^- against the incumbent)", 4: "Curve 4 (the frozen-funds extra)"}
    for c in (1, 2, 4):
        rs = [r for r in sp if r["curve"] == c]; hh = [r for r in rs if r["hyp"]]
        print(f"## {names[c]}")
        print(f"- points meeting the hypotheses (ETFs interior, budget slack at F, E^-, E^0): {len(hh)} of {len(rs)}"
              + (", excluded: " + ", ".join(f"cap {cp}: {sum(1 for r in rs if r['cap1'] == cp and not r['hyp'])}" for cp in (0.25, 1.0)) if c == 1 else ""))
        print(f"- C^- against the part 2 formula: {sum(ok(r, 'Cm', 'fC') for r in hh)}/{len(hh)} within tolerance; largest |difference| {max(abs(r['Cm'] - r['fC']) for r in hh):.1e}")
        print(f"- J^- - J^0 against the formula: {sum(ok(r, 'sale', 'fE') for r in hh)}/{len(hh)}; largest |difference| {max(abs(r['sale'] - r['fE']) for r in hh):.1e}")
        print(f"- C^0 = C^- + (J^- - J^0): largest residual {max(abs(r['C0'] - r['Cm'] - r['sale']) for r in hh):.1e}")
        print(f"- largest C^- {max(r['Cm'] for r in hh) * 1e4:.2f} bp; largest J^- - J^0 {max(r['sale'] for r in hh) * 1e4:.2f} bp; solver disagreement (both optimal) {max(dis(r) for r in rs):.1e}\n")
    # zero thresholds in curve 2
    rs = [r for r in sp if r["curve"] == 2 and r["hyp"]]
    rs2 = [r for r in rs if abs(r["a1"] - 0.002 - 5 * (0.02 ** 2 + 0.0035 ** 2) * r["xm1"]) >= 1e-9]
    zero_ok = sum((r["Cm"] <= dis(r) + ZERO) == (5 * (0.02 ** 2 + 0.0035 ** 2) * r["xm1"] >= r["a1"] - 0.002 or r["xm1"] >= r["cap1"]) for r in rs2)
    print(f"- curve 2: C^- = 0 iff gamma v x^- >= alpha_hat - kappa^+ or the incumbent is at its cap, at {zero_ok}/{len(rs2)} ({len(rs) - len(rs2)} knife-edge point with equality set aside)\n")
    P = S["premia"]; hh = [r for r in P if r["hyp"]]
    print("## Curve 3 (independence of the premia)")
    print(f"- {len(hh)} of {len(P)} (premium draw, fund draw) instances meet the hypotheses")
    print(f"- |C^- - formula| max {max(abs(r['Cm'] - r['fC']) for r in hh):.1e} (within tolerance {sum(ok(r, 'Cm', 'fC') for r in hh)}/{len(hh)}); "
          f"|J^- - J^0 - formula| max {max(abs(r['sale'] - r['fE']) for r in hh):.1e} ({sum(ok(r, 'sale', 'fE') for r in hh)}/{len(hh)})")
    out = [r for r in P if not r["hyp"]]
    print(f"- outside the hypotheses ({len(out)}): largest |C^- - formula| {max(abs(r['Cm'] - r['fC']) for r in out) * 1e4:.2f} bp\n")
    U = S["unreachable"]; hh = [r for r in U if r["hyp"]]
    print("## Curve 5 (missing exposure, part 3)")
    print(f"- {len(hh)} of {len(U)} meet the hypotheses; excluded by cap: " + ", ".join(f"cap {cp}: {sum(1 for r in U if r['cap1'] == cp and not r['hyp'])}" for cp in (0.25, 1.0)))
    print(f"- C^- against the reduced-moment formula: {sum(ok(r, 'Cm', 'fC') for r in hh)}/{len(hh)}; largest |difference| {max(abs(r['Cm'] - r['fC']) for r in hh):.1e}; "
          f"J^- - J^0: {sum(ok(r, 'sale', 'fE') for r in hh)}/{len(hh)}")
    for l2 in (-0.01, 0.005, 0.02):
        rs = [r for r in hh if r["l2"] == l2 and r["xm1"] == 0.0 and r["cap1"] == 0.25]
        z = [r["a1"] for r in rs if r["Cm"] > dis(r) + ZERO]
        print(f"  - lambda_hat_2 = {l2 * 100:+.1f}% (x^- = 0, cap 0.25): alpha^red - alpha_hat = {rs[0]['ared'] - rs[0]['a1']:.4f}; fund 1 bought (C^- > 0) from alpha_hat = {min(z) * 100 if z else float('nan'):.2f}%")
    print()
    Fr = S["frictions"]; hh = [r for r in Fr if r["hyp"]]
    print("## Curve 6 (ETF frictions, part 4)")
    print(f"- {len(hh)} of {len(Fr)} meet the hypotheses")
    inC = sum(r["Cl"] - dis(r) - TOL <= r["Cm"] <= r["Cu"] + dis(r) + TOL for r in hh)
    inE = sum(r["El"] - dis(r) - TOL <= r["sale"] <= r["Eu"] + dis(r) + TOL for r in hh)
    print(f"- C^- inside [lower, upper]: {inC}/{len(hh)}; J^- - J^0 inside its bracket: {inE}/{len(hh)}")
    print("| ETF rate | fee | points | C^- position in bracket: min / median / max (where upper > lower) | largest C^- (bp) |")
    print("|---|---|---|---|---|")
    for rE in (0, 0.0005, 0.001, 0.0025, 0.005):
        for fee in (0, 0.0005, 0.001):
            rs = [r for r in hh if r["rE"] == rE and r["fee"] == fee]
            pos = [(r["Cm"] - r["Cl"]) / (r["Cu"] - r["Cl"]) for r in rs if r["Cu"] - r["Cl"] > 1e-9]
            ps = f"{min(pos):.2f} / {np.median(pos):.2f} / {max(pos):.2f}" if pos else "-"
            print(f"| {rE * 1e4:.0f} bp | {fee * 1e4:.0f} bp | {len(rs)} | {ps} | {max(r['Cm'] for r in rs) * 1e4:.2f} |")
    bad = [r for r in hh if not (r["Cl"] - dis(r) - TOL <= r["Cm"] <= r["Cu"] + dis(r) + TOL)]
    for r in bad[:6]:
        print(f"  - outside: rate {r['rE']}, fee {r['fee']}, alpha {r['a1']}: C^- {r['Cm']:.3e} vs [{r['Cl']:.3e}, {r['Cu']:.3e}]")
    print()
    allr = [r for r in sp + P + U + Fr if r["hyp"]]
    edge = lambda r: r.get("a1") is not None and r.get("xm1") is not None and abs(r["a1"] - 0.002 - 5 * (0.02 ** 2 + 0.0035 ** 2) * r["xm1"]) < 1e-9
    body = [r for r in allr if not edge(r)]
    z1 = sum((r["Cm"] <= dis(r) + ZERO) == (not r["bought"]) for r in body)
    z0 = sum((r["C0"] <= dis(r) + ZERO) == (not r["traded"]) for r in body)
    print("## Part 1a")
    print(f"- C^- = 0 iff no fund bought at the joint optimum: {z1}/{len(body)}; C^0 = 0 iff no fund traded: {z0}/{len(body)} "
          f"(zero test at {ZERO:g}; {len(allr) - len(body)} knife-edge points with fund 1's purchase excess p_1 = 0 exactly set aside)")
    for r in [r for r in body if ((r["Cm"] <= dis(r) + ZERO) != (not r["bought"])) or ((r["C0"] <= dis(r) + ZERO) != (not r["traded"]))][:5]:
        print(f"  - mismatch: curve {r['curve']} a1 {r.get('a1')} xm1 {r.get('xm1')}: C^- {r['Cm']:.2e} bought {r['bought']}; C^0 {r['C0']:.2e} traded {r['traded']}")
    st = [s for r in sp + P + U + Fr for s in r["status"]]
    print(f"- statuses: {dict((s, st.count(s)) for s in set(st))} (the 15 'user_limit' are OSQP at its iteration cap; those points use CLARABEL alone); "
          f"largest disagreement where both are optimal {max(r['dis'] for r in sp + P + U + Fr if all(s == 'optimal' for s in r['status'])):.1e}")
    print(f"\nseconds: {S['seconds']:.0f}")
    figures(S)


def figures(S):
    import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    fig, axes = plt.subplots(1, 2, figsize=(10, 4))
    for ax, cap in zip(axes, (0.25, 1.0)):
        for xm in (0.0, 0.1, 0.2):
            rs = sorted([r for r in S["spanning"] if r["curve"] == 1 and r["xm1"] == xm and r["cap1"] == cap], key=lambda r: r["a1"])
            ax.plot([r["a1"] * 100 for r in rs], [r["fC"] * 1e4 for r in rs], label=f"formula, x^- = {xm}")
            hh = [r for r in rs if r["hyp"]]
            ax.plot([r["a1"] * 100 for r in hh][::6], [r["Cm"] * 1e4 for r in hh][::6], "k.", ms=3)
        ax.set_xlabel("alpha_hat_1 (% per quarter)"); ax.set_ylabel("C^- (bp)"); ax.set_title(f"Curve 1: ETF-only cost, fund 1 cap {cap}")
    axes[0].legend(fontsize=7); fig.tight_layout(); fig.savefig(HERE / "fig_curve1.png", dpi=130); plt.close(fig)
    fig, ax = plt.subplots(figsize=(6, 4))
    rs = sorted([r for r in S["spanning"] if r["curve"] == 4 and r["a1"] == -0.0019], key=lambda r: r["xm1"])
    for key, lab in (("Cm", "C^- (restriction proper)"), ("sale", "J^- - J^0 (value of permitted sales)"), ("C0", "C^0 (frozen funds)")):
        ax.plot([r["xm1"] for r in rs], [r[key] * 1e4 for r in rs], label=lab)
    ax.set_xlabel("fund 1 incumbent x^-_1"); ax.set_ylabel("bp per quarter"); ax.set_title("Curve 4: alpha_hat_1 = -0.19%, fund rate 20 bp (not the 50 bp equity-style point)"); ax.legend(fontsize=8)
    fig.tight_layout(); fig.savefig(HERE / "fig_curve4.png", dpi=130); plt.close(fig)


if __name__ == "__main__":
    main()
