"""Experiment 027 report: regime maps under the registered classification rules (uv run python experiments/027/report.py)."""
import json
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
N = 6
STARTS = ["all-ETF", "all-fund", "mixed"]
ANCHOR = {"EQ": dict(a=-0.19, s=0.35, sA=2.0, r=10.0, lamE=0.01, rho=1.0, f=1.0, D=1.0, menu="full"),
          "FI": dict(a=0.20, s=0.35, sA=1.0, r=0.5, lamE=0.1, rho=1.0, f=10.0, D=1.0, menu="missing")}


def diff(c, st, a, b):
    x = np.array(c["ce_bp"][st][a]) - np.array(c["ce_bp"][st][b])
    return x.mean(), x.std(ddof=1) / np.sqrt(len(x))


def fund_action(c, st, pol="MPC-L"):
    x0 = np.array(c["first_quarter"][st][pol])[:N]
    xs = {"all-ETF": np.zeros(N), "all-fund": np.full(N, 0.15), "mixed": np.full(N, 0.075)}[st]
    u = x0 - xs
    b = int((u > 1e-3).sum()); s = int((u < -1e-3).sum())
    h = int(((np.abs(u) <= 1e-3) & (x0 > 1e-3)).sum()); nh = N - b - s - h
    maj = max((("buy", b), ("sell", s), ("hold", h), ("none", nh)), key=lambda kv: kv[1])[0]
    return b, s, h, nh, maj


def l1(c, st, a, b):
    return float(np.abs(np.array(c["first_quarter"][st][a]) - np.array(c["first_quarter"][st][b])).sum())


def sgn(m, se):
    return "+" if m - 2 * se > 0 else "-" if m + 2 * se < 0 else "0"


def is_anchor(c):
    return all(abs(c["params"][k] - v) < 1e-9 if isinstance(v, float) else c["params"][k] == v for k, v in ANCHOR[c["anchor"]].items())


def main():
    C = json.load(open(HERE / "summary.json"))
    C.sort(key=lambda c: c["idx"])
    labels = {"S1": ("a", "r"), "S2": ("sA", "rho"), "S3": ("menu", "D"), "S4": ("f", "lamE")}
    print("Every input is an assumption (rule 22). * marks the anchor point (EQ or FI) within each slice.\n")
    for sl, (k1, k2) in labels.items():
        for anc in ("EQ", "FI"):
            cs = [c for c in C if c["slice"] == sl and c["anchor"] == anc]
            print(f"## Slice {sl} ({k1} x {k2}), anchor {anc}\n")
            print(f"| {k1} | {k2} | start | (b) MPC-L t=0: buy/sell/hold/none (majority) | fund-quarters held (MPC-L) | "
                  "(a) L1 MPC-L vs rule at t=0 | (a) MPC-L - rule, bp (SE) | learning MPC-L - MPC-S, bp | "
                  "(c) L1 two-stage vs rule at t=0 | (c) rule - two-stage, bp (SE) | MPC-L - ETF-only, bp (SE) | MPC-L - funds-only, bp (SE) | (d) premium sensitivity L1 |")
            print("|" + "---|" * 13)
            for c in cs:
                p = c["params"]
                for st in STARTS:
                    b, s, h, nh, maj = fund_action(c, st)
                    dr = diff(c, st, "MPC-L", "rule"); dl = diff(c, st, "MPC-L", "MPC-S")
                    d2 = diff(c, st, "rule", "two-stage"); de = diff(c, st, "MPC-L", "ETF-only"); df = diff(c, st, "MPC-L", "funds-only")
                    star = "*" if is_anchor(c) else ""
                    print(f"| {p[k1]}{star} | {p[k2]} | {st} | {b}/{s}/{h}/{nh} ({maj}) | {c['held'][st]['MPC-L']:.2f} | "
                          f"{l1(c, st, 'MPC-L', 'rule'):.4f} | {dr[0]:.3f} ({dr[1]:.3f}) | {dl[0]:.3f} | {l1(c, st, 'two-stage', 'rule'):.4f} | "
                          f"{d2[0]:.3f} ({d2[1]:.3f}) | {de[0]:.2f} ({de[1]:.2f}) | {df[0]:.2f} ({df[1]:.2f}) | "
                          f"{c['first_quarter']['premium_sensitivity_L1']:.4f} |")
            print()
    # region summaries under the registered rules
    print("## Region summaries (registered rules)\n")
    tot = len(C) * 3
    mat_a = [(c, st) for c in C for st in STARTS if l1(c, st, "MPC-L", "rule") > 0.01 or (lambda m, se: m - 2 * se > 1)(*diff(c, st, "MPC-L", "rule"))]
    print(f"- (a) dynamic/learning material (L1 > 0.01 at t=0, or MPC-L - rule > 1 bp at 2 SE): {len(mat_a)} of {tot} cell-starts")
    for c, st in mat_a[:40]:
        print(f"  - {c['slice']} {c['anchor']} {c['params']} {st}: L1 {l1(c, st, 'MPC-L', 'rule'):.4f}, CE {diff(c, st, 'MPC-L', 'rule')[0]:.3f} bp")
    ex = [(c, st) for c in C for st in STARTS if l1(c, st, "two-stage", "rule") <= 1e-6 and abs(diff(c, st, "rule", "two-stage")[0]) <= 2 * diff(c, st, "rule", "two-stage")[1]]
    print(f"- (c) two-stage exact (L1 <= 1e-6 at t=0 and CE within 2 SE): {len(ex)} of {tot}; loses (rule - two-stage > 2 SE): "
          f"{sum(1 for c in C for st in STARTS if sgn(*diff(c, st, 'rule', 'two-stage')) == '+')}")
    dd = [c for c in C if c["first_quarter"]["premium_sensitivity_L1"] > 0.01]
    print(f"- (d) premium error moves fund choice (L1 > 0.01 per prior SD): {len(dd)} of {len(C)} cells: "
          + "; ".join(f"{c['slice']} {c['anchor']} menu {c['params']['menu']} D {c['params']['D']}" for c in dd[:20]))
    for maj in ("buy", "sell", "hold", "none"):
        n = sum(1 for c in C for st in STARTS if fund_action(c, st)[4] == maj)
        print(f"- (b) majority action {maj}: {n} of {tot}")
    print(f"\nseconds per cell (sum): {sum(c['seconds'] for c in C):.0f}")


if __name__ == "__main__":
    main()
