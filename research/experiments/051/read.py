"""Experiment 051: the reserve today in experiment 048's cells (a reading; no solver). Run: uv run python experiments/051/read.py"""
import importlib.util
import json
from collections import defaultdict
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
_p = importlib.util.spec_from_file_location("presets", HERE.parent / "presets.py"); PR = importlib.util.module_from_spec(_p); _p.loader.exec_module(PR)
EPS = 1e-6


def cost(u, kA, kE):
    return kA * abs(u[0]) + kE * abs(u[1])


def revision(regime, unc):
    P = PR.PRESETS[regime]
    pl, pa = (P["premium_sd"][0] * unc) ** 2, (P["alpha_sd"] * unc) ** 2
    sf2, sa2 = P["factor_sd"][0] ** 2, P["sigma_A"] ** 2
    return dict(V_lambda=pl - 1 / (1 / pl + 1 / sf2), V_alpha=pa - 1 / (1 / pa + 1 / sa2), gain_alpha=pa / (pa + sa2), gain_lambda=pl / (pl + sf2))


def main():
    C = json.load(open(HERE.parent / "048" / "summary.json"))["cells"]
    rows = []; chk = 0.0
    for c in C:
        x0m = np.array(c["start"]); kA, kE = c["fund_rate"], c["etf_rate"]
        xd, xm = np.array(c["dynamic"]["x0"]), np.array(c["myopic"]["x0"])
        hd = c["cash"] - np.sum(xd - x0m) - cost(xd - x0m, kA, kE)
        hm_check = c["cash"] - np.sum(xm - x0m) - cost(xm - x0m, kA, kE); chk = max(chk, abs(hm_check - c["myopic"]["h0p"]))
        dE, dh, dA = xd[1] - xm[1], hd - c["myopic"]["h0p"], xd[0] - xm[0]
        where = ("ETF" if dE > EPS else "") + ("+cash" if dh > EPS else "")
        where = where.strip("+") or ("less ETF" if dE < -EPS else ("none" if abs(dh) <= EPS and abs(dA) <= EPS else "other"))
        rows.append(dict(regime=c["regime"], start=c["start"], cash=c["cash"], unc=c["unc"], costmul=c["costmul"], fund_rate=kA, etf_rate=kE,
                         cost_ratio=kA / kE, dE=float(dE), dh=float(dh), dA=float(dA), where=where, myopic_loss_bp=c["myopic"]["loss_bp"], binds=c["dynamic"]["binds"],
                         **revision(c["regime"], c["unc"])))
    json.dump(dict(rows=rows, cash_identity_check=chk), open(HERE / "reading.json", "w"), indent=1, default=float)
    print(f"cash identity reproduces myopic.h0p to {chk:.1e}\n")
    print("| regime | start (fund, ETF) | cash | ETF reserve x^dyn_E - x^my_E, range over the 6 (prior, cost) cells | cash reserve h^dyn - h^my, range | fund difference, range | where (count of 6) |")
    print("|---|---|---|---|---|---|---|")
    g = defaultdict(list)
    for r in rows:
        g[(r["regime"], tuple(r["start"]), r["cash"])].append(r)
    for (rg, st, ca), L in sorted(g.items()):
        f = lambda k: f"{min(r[k] for r in L):+.4f} to {max(r[k] for r in L):+.4f}"
        wc = defaultdict(int)
        for r in L:
            wc[r["where"]] += 1
        print(f"| {rg} | {st} | {'slack' if ca == 1.0 else 'tight'} | {f('dE')} | {f('dh')} | {f('dA')} | {dict(wc)} |")
    print("\nBy input level (counts of cells by where the reserve sits; mean ETF and cash reserve):")
    for key, lab in (("regime", "regime"), ("unc", "prior SD multiple"), ("costmul", "fund-rate multiple"), ("cash", "starting cash")):
        lv = defaultdict(list)
        for r in rows:
            lv[r[key]].append(r)
        for v, L in sorted(lv.items(), key=lambda t: str(t[0])):
            wc = defaultdict(int)
            for r in L:
                wc[r["where"]] += 1
            extra = f" (alpha revision variance {L[0]['V_alpha']:.2e}, gain {L[0]['gain_alpha']:.3f} in the first regime listed)" if key == "unc" else ""
            print(f"- {lab} = {v}: {dict(wc)}; mean dE {np.mean([r['dE'] for r in L]):+.4f}, mean dh {np.mean([r['dh'] for r in L]):+.4f}{extra}")
    print("\nCells with a nonzero reserve (|dE| or |dh| > 1e-6):")
    print("| regime | start | cash | prior x | fund rate x (fund/ETF rate ratio) | dE | dh | dA | myopic loss (bp) | budget binds (dynamic) |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for r in sorted(rows, key=lambda r: (r["regime"], r["start"], r["cash"], r["unc"], r["costmul"])):
        if abs(r["dE"]) > EPS or abs(r["dh"]) > EPS:
            print(f"| {r['regime']} | {tuple(r['start'])} | {'slack' if r['cash'] == 1.0 else 'tight'} | {r['unc']} | {r['costmul']} ({r['cost_ratio']:.2f}) | {r['dE']:+.4f} | {r['dh']:+.4f} | {r['dA']:+.4f} | {r['myopic_loss_bp']:.3f} | {r['binds']} |")


if __name__ == "__main__":
    main()
