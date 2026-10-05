"""Experiment 015, Deviation 1 (after seeing results; reporting only, no new solves).
Some cell brackets from `bracket` are inverted (the feasible-point CE exceeds the Frank-Wolfe bound) at the
1e-5 to 1e-4 bp level: floating-point and LP-tolerance error exceeds the true gap there. The registered
rule ("sign only if the interval excludes zero") is ill-defined for inverted intervals. Here each cell
bracket is replaced by [min(lo, hi) - tau, max(lo, hi) + tau], with tau = 10 x the largest inversion over
all cells, and every contribution is reclassified by the registered rule on these widened intervals.
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
rows = json.load(open(HERE / "results.json"))
inv = max(max(0.0, float(b[0]) - float(b[1])) for r in rows for b in r["brackets"].values() if b)
tau = 10 * inv
print(f"largest bracket inversion: {inv:.2e} bp; tau = {tau:.2e} bp\n")


def widened(r, c):
    lo, hi = (float(x) for x in r["brackets"][c])
    return min(lo, hi) - tau, max(lo, hi) + tau


def iv(r, plus, minus):
    return (sum(widened(r, c)[0] for c in plus) - sum(widened(r, c)[1] for c in minus),
            sum(widened(r, c)[1] for c in plus) - sum(widened(r, c)[0] for c in minus))


def sgn(i):
    return "+" if i[0] > 0 else "-" if i[1] < 0 else "?"


changed, counts = [], {}
print("| menu | costs | rho | tilt | ETF channel [widened] | active channel [widened] | class | registered class |")
print("|---|---|---|---|---|---|---|---|")
for r in rows:
    e = iv(r, ["FE", "EN"], ["EE", "FN"])
    a = iv(r, ["FF", "EE"], ["EF", "FE"])
    s = (sgn(e), sgn(a))
    cls = "claim-012 pattern" if s == ("+", "-") else ("unresolved" if "?" in s else f"FLIP {s}")
    old = (r["etf_sign"], r["act_sign"])
    oldc = "claim-012 pattern" if old == ("+", "-") else ("unresolved" if "?" in old else f"FLIP {old}")
    counts[cls.split(" (")[0] if cls.startswith("FLIP") else cls] = counts.get(cls.split(" (")[0] if cls.startswith("FLIP") else cls, 0) + 1
    if cls != oldc:
        changed.append((r["menu"], r["costs"], r["rho"], r["tilt"], oldc, cls))
    print(f"| {r['menu']} | {r['costs']} | {r['rho']} | {r['tilt']} | [{e[0]:+.4f}, {e[1]:+.4f}] | [{a[0]:+.4f}, {a[1]:+.4f}] | {cls} | {oldc} |")
print(f"\nclassifications changed by the widening: {len(changed)}")
for c in changed:
    print("-", c)
by_rho = {}
for r in rows:
    e, a = sgn(iv(r, ["FE", "EN"], ["EE", "FN"])), sgn(iv(r, ["FF", "EE"], ["EF", "FE"]))
    by_rho.setdefault(r["rho"], []).append((e, a))
for rho, v in sorted(by_rho.items()):
    print(f"rho {rho}: pattern {sum(x == ('+', '-') for x in v)}, flips {sum(x != ('+', '-') and '?' not in x for x in v)}, "
          f"unresolved {sum('?' in x for x in v)}, of {len(v)}")
