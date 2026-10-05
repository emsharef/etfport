"""Experiment 053 (D21): tables and the registered figure from summary.json.
Run: uv run python experiments/053/report.py   (after run.py)
Writes report.md and losses.png next to this file.
"""
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

HERE = Path(__file__).resolve().parent
C = json.load(open(HERE / "summary.json"))["cells"]
WELL = 0.01
STARTS = {(0.0, 0.9): "all-ETF", (0.15, 0.0): "all-fund", (0.075, 0.45): "mixed"}
INPUTS = [("revision_var", "alpha revision variance"), ("fund_buy", "fund's purchase rate"), ("etf_sell", "ETF's sale rate")]
POLICIES = [("myopic", lambda c: c["loss_my_bp"]), ("rule", lambda c: c["loss_rule_bp"]),
            ("Dev. 1: gate", lambda c: c["deviation1"]["gate"]["loss_bp"]),
            ("Dev. 1: own-point S_E", lambda c: c["deviation1"]["fixed_point"]["loss_bp"]),
            ("Dev. 1: both", lambda c: c["deviation1"]["gate_fixed_point"]["loss_bp"]),
            ("Dev. 1: band (3(b)'s exact display)", lambda c: c["deviation1"]["band"]["loss_bp"])]


def start(c):
    return STARTS[tuple(c["start"])]


def f(v, d=3):
    return "-" if v is None else f"{v:.{d}f}"


def summary_rows():
    out = ["| policy | works well (loss < 0.01 bp) | worse than myopic by > 0.01 bp | largest loss (bp) | recovery where myopic loses > 0.01 bp: median [min, max] |",
           "|---|---|---|---|---|"]
    for name, L in POLICIES:
        losses = [L(c) for c in C]; rec = [1 - L(c) / c["loss_my_bp"] for c in C if c["loss_my_bp"] > WELL]
        worse = "-" if name == "myopic" else str(sum(L(c) > c["loss_my_bp"] + WELL for c in C))
        r = "-" if name == "myopic" else f"{np.median(rec):.3f} [{min(rec):.3f}, {max(rec):.3f}] (n = {len(rec)})"
        out.append(f"| {name} | {sum(l < WELL for l in losses)}/{len(C)} | {worse} | {max(losses):.3f} | {r} |")
    return out


def cell_rows():
    out = ["| regime | start | cash | setting | myopic trades ETF | dyn binds | ETF: my -> dyn | reserve ETF dyn / rule / Dev.1 both | loss bp myopic / rule / Dev.1 both | rule clipped |",
           "|---|---|---|---|---|---|---|---|---|---|"]
    key = lambda c: (c["regime"], list(STARTS.values()).index(start(c)), -c["cash"], c["setting"], c["mult"])
    for c in sorted(C, key=key):
        d = c["deviation1"]["gate_fixed_point"]
        out.append(f"| {c['regime'].split('-')[0]} | {start(c)} | {c['cash']} | {c['setting']} x{c['mult']} | {'y' if c['myopic_trades_etf'] else 'n'} | "
                   f"{'y' if c['dyn_binds'] else 'n'} | {c['x_my'][1]:.4f} -> {c['x_dyn'][1]:.4f} | "
                   f"{c['reserve_dyn'][0]:+.4f} / {c['reserve_rule'][0]:+.4f} / {d['reserve'][0]:+.4f} | "
                   f"{f(c['loss_my_bp'])} / {f(c['loss_rule_bp'])} / {f(d['loss_bp'])} | {'y' if c['rule_clipped'] else 'n'} |")
    return out


def math_rows():
    out = ["| regime | start | cash | setting | h^my | N(x^my_0) | no-reserve check | Res | Pi_E sign (at x^my) | dyn - my: ETF, cash |",
           "|---|---|---|---|---|---|---|---|---|---|"]
    key = lambda c: (c["regime"], list(STARTS.values()).index(start(c)), -c["cash"], c["setting"], c["mult"])
    for c in sorted(C, key=key):
        m = c["math"]
        out.append(f"| {c['regime'].split('-')[0]} | {start(c)} | {c['cash']} | {c['setting']} x{c['mult']} | {m['h_my']:.4f} | {m['N_my']:.4f} | "
                   f"{'pass' if m['no_reserve_check'] else 'fail'} | {m['Res']:+.4f} | {m['Pi_E_sign_at_my'] or 'undefined'} | "
                   f"{c['reserve_dyn'][0]:+.4f}, {c['reserve_dyn'][1]:+.4f} |")
    return out


def figure():
    colors = {"all-ETF": "C0", "all-fund": "C1", "mixed": "C2"}
    styles = {"myopic": dict(ls="-", marker="o"), "rule": dict(ls="--", marker="s")}
    fig, ax = plt.subplots(2, 3, figsize=(12, 6.5), sharey="row")
    for i, regime in enumerate(("equity-style", "fixed-income-style")):
        for j, (inp, label) in enumerate(INPUTS):
            a = ax[i, j]
            for s in STARTS.values():
                for cash, fill in ((1.0, "full"), (0.005, "none")):
                    cs = [c for c in C if c["regime"] == regime and start(c) == s and c["cash"] == cash and c["setting"] in (inp, "preset")]
                    cs.sort(key=lambda c: c["mult"])
                    m = [c["mult"] for c in cs]
                    for pol, L in POLICIES[:2]:
                        a.plot(m, [max(L(c), 0.0) for c in cs], color=colors[s], fillstyle=fill, ms=5, **styles[pol])
            a.set_xscale("log", base=2); a.set_xticks(sorted({c["mult"] for c in C if c["setting"] == inp} | {1.0}))
            a.get_xaxis().set_major_formatter(matplotlib.ticker.FormatStrFormatter("x%g"))
            a.axhline(WELL, color="grey", lw=0.6, ls=":")
            a.set_title(f"{regime}: {label}", fontsize=9)
            if j == 0:
                a.set_ylabel("loss against the dynamic optimum (bp)")
    handles = [plt.Line2D([], [], color=colors[s], label=s) for s in STARTS.values()]
    handles += [plt.Line2D([], [], color="k", label=p, **styles[p]) for p in styles]
    handles += [plt.Line2D([], [], color="k", marker="o", ls="", fillstyle="none", label="tight cash (open)")]
    fig.legend(handles=handles, loc="lower center", ncol=6, fontsize=8, frameon=False)
    fig.suptitle("Experiment 053: myopic and claim 047's rule against the dynamic optimum, one input varied at a time "
                 "(illustration of the tested cells; the dotted line is 0.01 bp)", fontsize=9)
    fig.tight_layout(rect=(0, 0.05, 1, 0.96))
    fig.savefig(HERE / "losses.png", dpi=130)


def main():
    lines = ["# Experiment 053: tables (generated by report.py from summary.json)", "",
             "Losses are the dynamic optimum's expected objective minus the policy's, in bp. The rule is the registered one;",
             "Deviation 1's variants are post hoc and labelled. Tested cells only (AGENTS.md rule 22).", "",
             "## Summary", ""] + summary_rows() + ["", "## Cells", ""] + cell_rows() + ["", "## Claim 047's objects per cell (math's note; Deviation 4)", "",
                 "Pi_E's sign is the multiplier LP's range at the one-review root (experiment 052's part 3(a) computation); undefined where",
                 "the ETF is untraded today at x^my or h^my = 0. Res = F(x^dyn) - F(x^my), F = h + (1 - kappa^-_E) g^min_E p.", ""] + math_rows()
    (HERE / "report.md").write_text("\n".join(lines) + "\n")
    figure()
    print("\n".join(summary_rows()))


if __name__ == "__main__":
    main()
