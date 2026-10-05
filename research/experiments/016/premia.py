"""Experiment 016, Deviation 1 (a): claim 022's premium phi at the four root optimizers, in every instance.
Registered before any stage-1 result was read (PM note 2026-09-28-exp016-adjustable-wealth).

phi(u_0) = c_E(u_0) - c_N(u_0) is computed by re-solving the node problems with the root fixed, using
math's `solve_fixed` and `beta` from checks/exp015-premia/check.py (reused with attribution) at the four
optimizers A_N, A_E (full root) and B_N, B_E (ETF-only root) stored in results.json (funded projections).
Floating CLARABEL solves, not certificates. Reported:
- the sandwich phi(A_N) - phi(B_E) <= channel <= phi(A_E) - phi(B_N) against the certified channel interval;
- the funded cap phi <= beta;
- the funded rule, sign(channel) = sign(adjustable(A_E) - adjustable(B_N)), with every exception listed.

Run: uv run python -W ignore experiments/016/premia.py   (writes experiments/016/premia.json)
"""
from __future__ import annotations

import importlib.util
import json
import os
import sys
from fractions import Fraction as F
from multiprocessing import Pool
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


r16 = _load("r16", HERE / "run.py")
math015 = _load("math015", ROOT / "checks" / "exp015-premia" / "check.py")
OPT = {"A_N": "FN", "A_E": "FE", "B_N": "EN", "B_E": "EE"}


def task(row):
    if any(row["cells"][c] is None for c in OPT.values()):
        return None
    I = r16.build(row)
    B = r16.bayes(I)
    out = {}
    for name, c in OPT.items():
        u0 = row["cells"][c]["u0"]
        cE, h = math015.solve_fixed(I, B, u0, "E")
        cN, _ = math015.solve_fixed(I, B, u0, "N")
        out[name] = dict(phi=(cE - cN) * 1e4, beta=math015.beta(I, u0, h) * 1e4,
                         adjustable=row["cells"][c]["adjustable"])
    return out


def main():
    rows = json.load(open(HERE / "results.json"))
    if not (HERE / "premia.json").exists():
        with Pool(int(os.environ.get("PROCS", "8"))) as pool:
            res = pool.map(task, rows, chunksize=4)
        (HERE / "premia.json").write_text(json.dumps(res, indent=0))
    res = json.load(open(HERE / "premia.json"))
    brs = [c["bracket"] for r in rows for c in r["cells"].values() if c and c["bracket"]]
    brs += [p[k] for r in rows for p in r["grid"] for k in ("WE", "WN") if p[k]]
    tau = 10 * max(max(0.0, b[0] - b[1]) for b in brs)
    TOL = 2e-1   # bp: floating tolerance for the sandwich and cap (solver outputs, not certificates)
    cap = sand = 0
    exc, stats = [], {}
    for r, p in zip(rows, res):
        fam = r["family"]
        s = stats.setdefault(fam, dict(n=0, agree=0, exc=0, unresolved=0, noprd=0))
        s["n"] += 1
        if p is None:
            s["unresolved"] += 1
            continue
        cb = {k: (min(v["bracket"]) - tau, max(v["bracket"]) + tau) if v and v["bracket"] else None
              for k, v in r["cells"].items()}
        if any(cb[k] is None for k in ("FE", "EN", "EE", "FN")):
            s["unresolved"] += 1
            continue
        lo = cb["FE"][0] + cb["EN"][0] - cb["EE"][1] - cb["FN"][1]
        hi = cb["FE"][1] + cb["EN"][1] - cb["EE"][0] - cb["FN"][0]
        cs = "+" if lo > 0 else "-" if hi < 0 else "?"
        slo, shi = p["A_N"]["phi"] - p["B_E"]["phi"], p["A_E"]["phi"] - p["B_N"]["phi"]
        sand += not (slo - TOL <= hi and lo <= shi + TOL)
        cap += sum(not (-TOL <= v["phi"] <= v["beta"] + TOL) for v in p.values())
        d = p["A_E"]["adjustable"] - p["B_N"]["adjustable"]
        pred = "0" if abs(d) <= 1e-6 else "+" if d > 0 else "-"
        if cs == "?":
            s["unresolved"] += 1
        elif pred == "0":
            s["noprd"] += 1
        elif pred == cs:
            s["agree"] += 1
        else:
            s["exc"] += 1
            exc.append((r, cs, lo, hi, p, slo, shi))
    print("## Funded rule: sign(channel) = sign(adjustable(A_E) - adjustable(B_N))\n")
    print("| family | instances | agree | exceptions | channel unresolved | adjustable equal (no prediction) |")
    print("|---|---|---|---|---|---|")
    for fam, s in stats.items():
        print(f"| {fam} | {s['n']} | {s['agree']} | {s['exc']} | {s['unresolved']} | {s['noprd']} |")
    print(f"\nsandwich violations beyond {TOL} bp: {sand}; cap violations (of 4 optimizers each): {cap}\n")
    print("## Every exception\n")
    for r, cs, lo, hi, p, slo, shi in exc:
        c = r["cells"]
        print(f"- {r['family']} | {r['cost']} | {r['tilt']} | rho {r['rho']} | a0 {float(F(r['a0'])):.3f}: channel {cs} "
              f"[{lo:+.4f}, {hi:+.4f}] bp; adjustable A_E {p['A_E']['adjustable']:.4f} vs B_N {p['B_N']['adjustable']:.4f}; "
              f"phi A_N/A_E/B_N/B_E {p['A_N']['phi']:.3f}/{p['A_E']['phi']:.3f}/{p['B_N']['phi']:.3f}/{p['B_E']['phi']:.3f} bp; "
              f"sandwich [{slo:+.3f}, {shi:+.3f}]; root trades A_E {c['FE']['dirA']}/{c['FE']['dirE']}, "
              f"A_N {c['FN']['dirA']}/{c['FN']['dirE']}, B_N ETF {c['EN']['dirE']}, B_E ETF {c['EE']['dirE']}; "
              f"A_E cash {c['FE']['cash']:.4f} ETF {c['FE']['etf']:.4f}; B_N cash {c['EN']['cash']:.4f} ETF {c['EN']['etf']:.4f}")
    print(f"\nexceptions: {len(exc)}")


if __name__ == "__main__":
    main()
