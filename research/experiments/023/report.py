"""Experiment 023 report: claim 029's checks on Parts A and B (uv run python experiments/023/report.py)."""
import json
import statistics
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent


def part_b():
    R = json.load(open(HERE / "partB.json"))
    print("## Part B: generic M6 target (one instrument; exact on its lattice; tolerances in grid steps h = static/200)\n")
    print("| law | costs | s/static | T | cap | class | interior bands | max width/static | last review: max edge error (h) | "
          "coarse: max edge error vs shifted static band (h) | fine: min / median width/static |")
    print("|---|---|---|---|---|---|---|---|---|---|---|")
    viol = []
    fine_rows = []
    for c in R:
        recs = [r for r in c["records"] if r["interior"]]
        if not recs:
            continue
        T = c["T"]
        mx = max(r["width_ratio"] for r in recs)
        if mx > 1 + 2 * c["h"] / c["static"]:
            viol.append(("ceiling", c["law"], c["cost"], c["ratio"], T, c["capped"], mx))
        last = [r for r in recs if r["t"] == T - 1]
        e_last = max(max(abs(r["dev_lo_h"]), abs(r["dev_hi_h"])) for r in last) if last else None
        if e_last is not None and e_last > 1:
            viol.append(("last review", c["law"], c["cost"], c["ratio"], T, c["capped"], e_last))
        early = [r for r in recs if r["t"] < T - 1]
        cls = "coarse (1d holds)" if c["coarse_sufficient"] else ("boundary" if c["on_boundary"] else "fine")
        e_coarse, fine_s = "-", "-"
        if early and c["coarse_sufficient"]:
            e = max(max(abs(r["dev_lo_h"]), abs(r["dev_hi_h"])) for r in early)
            e_coarse = f"{e:.2f}"
            if e > 1:
                viol.append(("coarse edges", c["law"], c["cost"], c["ratio"], T, c["capped"], e))
        elif early:
            ws = [r["width_ratio"] for r in early]
            fine_s = f"{min(ws):.3f} / {statistics.median(ws):.3f}"
            if not c["on_boundary"]:
                eq = [r for r in early if abs(r["width_ratio"] - 1) <= 2 * c["h"] / c["static"]]
                fine_rows.append((c, early, eq))
        print(f"| {c['law']} | {c['cost']} | {c['ratio']} | {T} | {'x0+0.5 static' if c['capped'] else 'none'} | {cls} | {len(recs)} | "
              f"{mx:.4f} | {'-' if e_last is None else f'{e_last:.2f}'} | {e_coarse} | {fine_s} |")
    print(f"\n**Violations of claim 029 beyond tolerance:** {len(viol)}")
    for v in viol:
        print(f"- {v}")
    # exact 1e test (Deviation 2 iii): for every interior band before the last review, straddle vs the next bands
    agree = eq_str = nar_nostr = total = 0
    examples = []
    for c in R:
        steps = {"symmetric": [1, -1], "skewed": [4, -1]}[c["law"]]
        byk = {(r["t"], r["k"]): r for r in c["records"]}
        h = c["h"]
        for r in c["records"]:
            if not r["interior"] or r["t"] >= c["T"] - 1:
                continue
            nxt = [byk.get((r["t"] + 1, r["k"] + st)) for st in steps]
            if any(x is None for x in nxt):
                continue
            straddle = any(not (r["hi"] <= x["lo"] + h or r["lo"] >= x["hi"] - h) for x in nxt)
            full = abs(r["width_ratio"] - 1) <= 2 * h / c["static"]
            total += 1
            if full and straddle:
                eq_str += 1
                if len(examples) < 5:
                    examples.append((c["law"], c["cost"], c["ratio"], c["T"], c["capped"], r["t"], r["k"], round(r["width_ratio"], 4)))
            elif (not full) and (not straddle) and r["width_ratio"] < 1 - 2 * h / c["static"]:
                nar_nostr += 1
            else:
                agree += 1
    print(f"\n**Exact 1e test (Part B; Deviation 2):** {total} interior bands before the last review with all next bands "
          f"available. 1e's equivalence (width = static iff no straddling outcome) holds in {agree}. Full width despite a "
          f"straddling outcome: {eq_str}. Narrower with no straddling outcome: {nar_nostr}.")
    for e in examples:
        print(f"- full width with straddle: {e}")

    # cube-root scale, fine cells: width / (s^(2/3) (k+ + k-)^(1/3) / c^(1/3)), bands at t = 0
    print("\n**Cube-root scale (fine cells, t = 0, symmetric law, no cap):** width / [s^(2/3) (kappa^+ + kappa^-)^(1/3) / c^(1/3)]\n")
    print("| costs | s/static | T | width/static | ratio to cube-root scale |")
    print("|---|---|---|---|---|")
    C = 5.0 * 0.0854 ** 2
    for c in R:
        if c["law"] != "symmetric" or c["capped"] or c["coarse_sufficient"]:
            continue
        r0 = [r for r in c["records"] if r["t"] == 0 and r["interior"]]
        if not r0:
            continue
        w = r0[0]["width_ratio"] * c["static"]
        k = c["static"] * C
        scale = c["s"] ** (2 / 3) * k ** (1 / 3) / C ** (1 / 3)
        print(f"| {c['cost']} | {c['ratio']} | {c['T']} | {r0[0]['width_ratio']:.3f} | {w / scale:.3f} |")


def exact_centre_slope(c, j, xes):
    """Deviation 3: slope, over the ETF holdings used, of the centre of claim 029 part 2c's parallelotope section along
    fund 1 (fund 2 at its grid target), from the same instance, belief point and grid (no DP)."""
    import sys
    sys.path.insert(0, str(HERE.parent / "021")); sys.path.insert(0, str(HERE))
    from model import Inst
    import partA
    I = Inst("P2", *partA.SPECS["P2"], partA.GAMMA, c["T"])
    t = c["T"] - 1
    S = I.S(t)
    mg = partA.mgrid(I)
    m = I.m0().copy(); m[0] = mg[j]
    mu = I.H() @ m + I.g0()
    kap = np.array([c["kappa_fund"]] * I.N + [c["kappa_etf"]] * I.M)
    h = c["h"]; xs = np.round(np.arange(round(1 / h) + 1) * h, 12)
    X = np.meshgrid(*([xs] * 3), indexing="ij"); xf = np.stack([x.ravel() for x in X], 1)
    one = (xf @ mu - 0.5 * partA.GAMMA * np.einsum("pi,ij,pj->p", xf, S, xf)).reshape(X[0].shape)
    tg = np.unravel_index(np.argmax(one), X[0].shape)
    xstar = np.linalg.solve(partA.GAMMA * S, mu)
    cen = []
    for xe in xes:
        tgt = [None, xs[tg[1]], xe]
        lo, hi = 0.0, 1.0
        for k in range(3):
            base = partA.GAMMA * sum(S[k, l] * (tgt[l] - xstar[l]) for l in (1, 2)) - partA.GAMMA * S[k, 0] * xstar[0]
            a = partA.GAMMA * S[k, 0]
            lower_ok = not (k != 0 and tgt[k] >= 1.0); upper_ok = not (k != 0 and tgt[k] <= 0.0)
            if lower_ok:
                lo = max(lo, (-kap[k] - base) / a)
            if upper_ok:
                hi = min(hi, (kap[k] - base) / a)
        cen.append((lo + hi) / 2)
    return float(np.polyfit(xes, cen, 1)[0])


def part_a():
    R = json.load(open(HERE / "partA.json"))
    print("\n## Part A: experiment 021's P1 and P2 (claim checks on the no-trade-set section; Deviation 1)\n")
    print("| instance | kappa fund (bp) | T | h | instrument | bands (NT interior) | max NT width/static | "
          "NT width / 2c section at t=T-1 (min-max) | coarse / fine / unresolved vs section (t<T-1) | median r = sd(innovation)/static | max own-band width/static |")
    print("|---|---|---|---|---|---|---|---|---|---|---|")
    viol = []
    fine_pts = []
    for c in R:
        for inst in sorted({r["inst"] for r in c["records"]}):
            rs = [r for r in c["records"] if r["inst"] == inst]
            nt = [r for r in rs if r["nt_interior"] and r["nt_width"] is not None]
            name = ("fund 1" if inst == 0 else ("fund 2" if (c["inst"] == "P2" and inst == 1) else "ETF"))
            if not nt:
                continue
            h = c["h"]
            mx = max(r["nt_width"] / r["static"] for r in nt)
            for r in nt:
                if r["nt_width"] > r["static"] + 2 * h:
                    viol.append(("ceiling 2b", c["inst"], c["kappa_fund"], c["T"], h, name, r["t"], r["nt_width"] / r["static"]))
            last = [r["nt_width"] / r["section"] for r in nt if r["t"] == c["T"] - 1 and r["section"] > 0]
            for r in nt:
                if r["t"] == c["T"] - 1 and abs(r["nt_width"] - r["section"]) > 2 * h:
                    viol.append(("last review 2c", c["inst"], c["kappa_fund"], c["T"], h, name, r["t"], r["nt_width"], r["section"]))
            early = [r for r in nt if r["t"] < c["T"] - 1]
            unres = [r for r in early if r["section"] < 3 * h]
            ok = [r for r in early if r["section"] >= 3 * h]
            coarse = [r for r in ok if abs(r["nt_width"] - r["section"]) <= 2 * h]
            fine = [r for r in ok if r["nt_width"] < r["section"] - 2 * h]
            fine_pts += [(c, r) for r in fine]
            rr = statistics.median([r["sd_innov"] / r["static"] for r in rs])
            own = max((r["own_width"] or 0) / r["static"] for r in rs)
            print(f"| {c['inst']} | {c['kappa_fund'] * 1e4:.0f} | {c['T']} | 1/{round(1 / h)} | {name} | {len(nt)} | {mx:.3f} | "
                  f"{(f'{min(last):.3f}-{max(last):.3f}') if last else '-'} | {len(coarse)} / {len(fine)} / {len(unres)} | {rr:.3f} | {own:.3f} |")
    from collections import Counter
    print(f"\n**Violations of claim 029 beyond 2h:** {len(viol)} {dict(Counter(v[0] for v in viol))}")
    for v in viol[:40]:
        print(f"- {v}")
    # 2c slope in P2
    print("\n**Part 2c (P2, t = T-1):** slope of the fund-1 no-trade-section centre on the ETF holding, per belief point, "
          "against -S_1E/S_11\n")
    print("| kappa fund (bp) | T | h | belief points | median slope | range | -S_1E/S_11 (fund face) | exact 2c section centre slope (median) |")
    print("|---|---|---|---|---|---|---|---|")
    for c in R:
        if c["inst"] != "P2" or not c["centre_points"]:
            continue
        by = {}
        for j, xe, cen in c["centre_points"]:
            by.setdefault(j, []).append((xe, cen))
        sl, ex = [], []
        for j, v in by.items():
            if len({p[0] for p in v}) < 3:
                continue
            sl.append(np.polyfit([p[0] for p in v], [p[1] for p in v], 1)[0])
            ex.append(exact_centre_slope(c, j, [p[0] for p in v]))      # Deviation 3
        if sl:
            print(f"| {c['kappa_fund'] * 1e4:.0f} | {c['T']} | 1/{round(1 / c['h'])} | {len(sl)} | {statistics.median(sl):.3f} | "
                  f"{min(sl):.3f} to {max(sl):.3f} | {c['predicted_slope']:.3f} | {statistics.median(ex):.3f} |")
    # cube-root scale on fine P1 cells
    print("\n**Fine cells in P1 (h = 1/400): width against the cube-root scale** s^(2/3) (2 kappa)^(1/3) / c^(1/3)\n")
    print("| instrument | kappa (bp) | T | cells | median width/static | median ratio to cube-root scale |")
    print("|---|---|---|---|---|---|")
    groups = {}
    for c, r in fine_pts:
        if c["inst"] == "P1" and abs(c["h"] - 1 / 400) < 1e-12:
            groups.setdefault(("fund" if r["inst"] == 0 else "ETF", r["kappa"], c["T"]), []).append(r)
    for (nm, k, T), rs in sorted(groups.items()):
        rat = [r["nt_width"] / (r["sd_innov"] ** (2 / 3) * (2 * r["kappa"]) ** (1 / 3) / r["c"] ** (1 / 3)) for r in rs]
        print(f"| {nm} | {k * 1e4:.0f} | {T} | {len(rs)} | {statistics.median([r['nt_width'] / r['static'] for r in rs]):.3f} | "
              f"{statistics.median(rat):.3f} |")


if __name__ == "__main__":
    part_b()
    part_a()
