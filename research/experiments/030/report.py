"""Experiment 030 report and figures (uv run python experiments/030/report.py), from summary.json."""
import json
from collections import Counter
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
TOL = 1e-8
GAMMA = 5.0


def main():
    S = json.load(open(HERE / "summary.json"))
    print("Tolerance: solvers' disagreement + 1e-8 (objective units) and 1e-8 in holdings unless stated.\n")
    # curve 1
    rows = [(d, r) for d in S["c1"] for r in d["rows"]]
    hh = [(d, r) for d, r in rows if d["hyp"] and r["hyp"]]
    print("## Curve 1 (part 1: spanning, frictionless ETFs; +-1 SD premium shifts)")
    print(f"- shifts where base and shifted optima meet the hypotheses: {len(hh)} of {len(rows)} (draws with a hypothesis-meeting base: {sum(d['hyp'] for d in S['c1'])} of 200)")
    print(f"- largest fund-holding L1 change {max(r['fundL1'] for _, r in hh):.2e} (claim: 0); within 1e-8: {sum(r['fundL1'] <= 1e-8 for _, r in hh)}/{len(hh)}")
    print(f"- largest error of the exposure change against (gamma Sigma~_f)^-1 delta: {max(r['expo_err'] for _, r in hh):.2e}")
    out = [r for d, r in rows if not (d["hyp"] and r["hyp"])]
    print(f"- outside the hypotheses ({len(out)} shifts; an ETF at a bound or budget binding): largest fund L1 change {max(r['fundL1'] for r in out):.3f}")
    print(f"- solver disagreement: objective {max(r['dQ'] for _, r in rows):.1e}, holdings {max(r['dx'] for _, r in rows):.1e}; non-optimal {sum(any(s != 'optimal' for s in r['status']) for _, r in rows)}\n")
    # curve 2
    C = S["c234"]; h2 = [r for r in C if r["hyp"]]
    print("## Curve 2 (part 2b: one unreachable fund)")
    print(f"- points meeting the hypotheses: {len(h2)} of {len(C)}; excluded by cap: " + ", ".join(f"cap {c}: {sum(1 for r in C if r['cap'] == c and not r['hyp'])}" for c in (0.25, 1.0)))
    print(f"- |solved holding - a_i(lambda_hat)|: max {max(abs(r['x1'] - r['f_hold']) for r in h2):.2e}; within 1e-8: {sum(abs(r['x1'] - r['f_hold']) <= 1e-8 for r in h2)}/{len(h2)}; "
          f"within the solvers' holding disagreement + 1e-8: {sum(abs(r['x1'] - r['f_hold']) <= r['dx'] + 1e-8 for r in h2)}/{len(h2)}")
    g = [r for r in h2 if r["grad_ok_region"]]
    ge = [abs(r["grad"] - r["f_grad"]) / max(abs(r["f_grad"]), 1.0) for r in g]
    print(f"- gradient in lambda_hat_2 (central differences, step 1e-4; {len(g)} points away from kinks): largest |error| {max(ge):.2e} (relative to max(|formula|, 1)); "
          f"trading-piece formula J B^A'/(gamma s^red) at {sum(r['f_grad'] != 0 for r in g)} points, zero at {sum(r['f_grad'] == 0 for r in g)}")
    print(f"- solver disagreement: objective {max(r['dQ'] for r in C):.1e}, holdings {max(r['dx'] for r in C):.1e}\n")
    # curves 3-4
    E = [(r, e) for r in C for e in r["errs"]]
    Eh = [(r, e) for r, e in E if e["hyp"]]
    print("## Curve 3 (part 2c: decision change; the Statement as corrected on main, Deviation 4)")
    print(f"- held base points: {sum(1 for r in C if r['errs'])}; error cases {len(E)}, meeting the hypotheses {len(Eh)}")
    ne = [(r, e) for r, e in Eh if not e["edge"]]
    agree = sum(e["dec"] == e["pred"] for _, e in ne)
    print(f"- solved decision = Statement's prediction: {agree}/{len(ne)} off the knife edges; knife-edge cases (|m + delta - band edge| < 1e-7): {len(Eh) - len(ne)}")
    print(f"- decisions: {dict(Counter(e['dec'] for _, e in ne))}; changed from hold: {sum(e['dec'] != 'hold' for _, e in ne)}")
    for r, e in [(r, e) for r, e in ne if e["dec"] != e["pred"]][:8]:
        print(f"  - mismatch: {r['name']} rate {r['rate']} xm {r['xm']} cap {r['cap']} l2 {r['l2']} t {e['t']}: solved {e['dec']}, predicted {e['pred']}")
    small = [(r, e) for r, e in ne if e["dec"] != "hold"]
    print(f"- no change with |delta| <= slack: violations {sum(1 for r, e in ne if e['dec'] != 'hold' and abs(e['delta']) <= slack_of(r) - 1e-9)}\n")
    print("## Curve 4 (part 2d: cost)")
    lo = sum(e["loss"] >= -e.get("dQ", 0) - TOL for _, e in Eh); up = sum(e["loss"] <= e["upper"] + e.get("dQ", 0) + TOL for _, e in Eh)
    db = sum(abs(e["D"]) <= e["Dbound"] + 1e-7 for _, e in Eh)
    print(f"- 0 <= loss: {lo}/{len(Eh)}; loss <= (gamma s^red/2) D^2 + (kappa^+ + kappa^- + mu) |D|: {up}/{len(Eh)}; |D| <= |delta|/(gamma s^red): {db}/{len(Eh)}")
    print(f"- largest loss {max(e['loss'] for _, e in Eh) * 1e4:.3f} bp; largest loss / upper {max(e['loss'] / e['upper'] for _, e in Eh if e['upper'] > 1e-12):.3f}")
    for nm, d in S["mc"].items():
        L = np.array([x[0] for x in d["draws"]]); dis = [x[1] for x in d["draws"] if len(x) > 1]
        ell = 0.5 * 0.005; v = 0.02 ** 2 + 0.0035 ** 2; sred = v + 0.25 * (0.04 ** 2 + 0.005 ** 2)
        kp = {"equity-style": 0.005, "fixed-income-style": 0.002}[nm]
        ared = {"equity-style": -0.0019, "fixed-income-style": 0.0020}[nm] + 0.5 * 0.005
        a_true = np.clip(np.clip(d["xm"], (ared - kp) / (GAMMA * sred), (ared + kp) / (GAMMA * sred)), 0, d["cap"])
        bound = ell ** 2 / (2 * GAMMA * sred) + 2 * kp * ell / (GAMMA * sred)
        interior = 0 < a_true < d["cap"]
        print(f"- expected loss, {nm} (x^- = {d['xm']}, cap {d['cap']}; a(lambda) = {a_true:.4f}, {'interior' if interior else 'at a bound: the bound is not claimed'}): "
              f"MC {L.mean() * 1e4:.4f} bp (SE {L.std(ddof=1) / np.sqrt(len(L)) * 1e4:.4f}; {len(L)} draws) against the bound {bound * 1e4:.4f} bp; "
              f"OSQP disagreement on {len(dis)} draws {max(dis):.1e}")
    print()
    # curve 5
    print("## Curve 5 (part 3: naive total-return rule)")
    for key in ("c5_draws", "c5_sweep"):
        R = S[key]; hh = [r for r in R if r["hyp"]]
        print(f"- {key}: {len(hh)} of {len(R)} meet the hypotheses; |solved loss - Lambda^naive| max {max(abs(r['loss'] - r['form']) for r in hh):.2e} "
              f"(within tolerance {sum(abs(r['loss'] - r['form']) <= r['dQ'] + TOL for r in hh)}/{len(hh)}); naive holdings vs clip max {max(r['hold_err'] for r in R):.1e}; "
              f"negative-alpha funds bought naively {sum(r['neg_bought'] for r in hh)}; largest Lambda^naive {max(r['form'] for r in hh) * 1e4:.2f} bp")
    for nm in ("equity-style", "fixed-income-style"):
        rs = [r for r in S["c5_sweep"] if r["name"] == nm and r["hyp"]]
        if rs:
            print(f"  - {nm}: lambda_hat_1 in [{min(r['l1'] for r in rs) * 100:.1f}, {max(r['l1'] for r in rs) * 100:.1f}]% meets the hypotheses; Lambda^naive from {min(r['form'] for r in rs) * 1e4:.2f} to {max(r['form'] for r in rs) * 1e4:.2f} bp")
    print()
    # curve 6
    print("## Curve 6 (outside the hypotheses; illustration only)")
    print("Fund-holding L1 change per 1 SD premium shift (largest of four shifts). 'no bound' = the largest over shifts whose optimum has no ETF at a bound and a slack budget (base too); '-' when none qualifies.")
    print("| point | sweep | level | ETF bounds | all shifts | no bound (n of 4) | base: ETF at bound / budget binding |")
    print("|---|---|---|---|---|---|---|")
    for r in S["c6"]:
        lv = f"{r['level'] * 1e4:.0f} bp" if r["kind"] == "etf_rate" else f"h = {r['level']}"
        cl = "-" if r["L1_clean"] is None else f"{r['L1_clean']:.4f}"
        print(f"| {r['name']} | {r['kind']} | {lv} | {'relaxed (-1, 2)' if r['relaxed'] else '[0, 1]'} | {r['L1_all']:.4f} | {cl} ({r['n_clean']}) | {r['base_etf_bound']} / {r['base_budget']} |")
    print(f"\nseconds: {S['seconds']:.0f}")
    figures(S)


def slack_of(r):
    v = 0.02 ** 2 + 0.0035 ** 2; sred = v + 0.25 * (0.04 ** 2 + 0.005 ** 2)
    a0 = {"equity-style": -0.0019, "fixed-income-style": 0.0020}[r["name"]]
    m = a0 + 0.5 * r["l2"] - GAMMA * sred * r["xm"]
    return min(r["rate"] - m, m + r["rate"])


def figures(S):
    import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    fig, axes = plt.subplots(1, 2, figsize=(10, 4))
    for ax, nm in zip(axes, ("equity-style", "fixed-income-style")):
        for rt in (0.0, 0.002, 0.01):
            rs = sorted([r for r in S["c234"] if r["name"] == nm and r["rate"] == rt and r["xm"] == 0.15 and r["cap"] == 0.25], key=lambda r: r["l2"])
            ax.plot([r["l2"] * 100 for r in rs], [r["f_hold"] for r in rs], label=f"formula, fund rate {rt * 1e4:.0f} bp")
            ax.plot([r["l2"] * 100 for r in rs if r["hyp"]][::6], [r["x1"] for r in rs if r["hyp"]][::6], "k.", ms=3)
        ax.set_xlabel("lambda_hat_2, the unreachable premium (% per quarter)"); ax.set_ylabel("fund 1 holding"); ax.set_title(f"Curve 2: {nm}, x^- = 0.15, cap 0.25")
    axes[0].legend(fontsize=7); fig.tight_layout(); fig.savefig(HERE / "fig_curve2.png", dpi=130); plt.close(fig)
    fig, ax = plt.subplots(figsize=(6, 4))
    for nm in ("equity-style", "fixed-income-style"):
        rs = sorted([r for r in S["c5_sweep"] if r["name"] == nm], key=lambda r: r["l1"])
        ax.plot([r["l1"] * 100 for r in rs], [r["form"] * 1e4 for r in rs], label=f"{nm}: Lambda^naive (formula)")
        ax.plot([r["l1"] * 100 for r in rs if r["hyp"]], [r["loss"] * 1e4 for r in rs if r["hyp"]], "k.", ms=3)
    ax.set_xlabel("lambda_hat_1 (% per quarter)"); ax.set_ylabel("bp per quarter"); ax.set_title("Curve 5: naive total-return rule's loss"); ax.legend(fontsize=7)
    fig.tight_layout(); fig.savefig(HERE / "fig_curve5.png", dpi=130); plt.close(fig)
    fig, axes = plt.subplots(1, 2, figsize=(10, 4))
    for ax, kind in zip(axes, ("etf_rate", "budget")):
        for nm in ("equity-style", "fixed-income-style"):
            for rx, st in ((False, "-"), (True, "--")):
                rs = sorted([r for r in S["c6"] if r["name"] == nm and r["kind"] == kind and r["relaxed"] == rx], key=lambda r: r["level"])
                ax.plot([r["level"] * (1e4 if kind == "etf_rate" else 1) for r in rs], [r["L1_all"] for r in rs], st, marker="o", ms=3,
                        label=f"{nm}, ETF bounds {'relaxed' if rx else '[0, 1]'}")
        ax.set_xlabel("ETF proportional rate (bp)" if kind == "etf_rate" else "cash h^- (ETF incumbents 0)"); ax.set_ylabel("fund L1 change per 1 SD premium shift")
        ax.set_title("Curve 6 (outside the hypotheses)")
    axes[0].legend(fontsize=6); fig.tight_layout(); fig.savefig(HERE / "fig_curve6.png", dpi=130); plt.close(fig)


if __name__ == "__main__":
    main()
