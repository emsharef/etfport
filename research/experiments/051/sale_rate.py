"""Experiment 051, Deviation 1: the reserve against the ETF's sale rate on 048's 18 fixed-income-style cells with a
material reserve. Run: uv run python experiments/051/sale_rate.py"""
import importlib.util
import itertools
import json
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "d16-harness"))
from harness import m8_model  # noqa: E402

_p = importlib.util.spec_from_file_location("presets", HERE.parent / "presets.py"); PR = importlib.util.module_from_spec(_p); _p.loader.exec_module(PR)
_e = importlib.util.spec_from_file_location("run047", HERE.parent / "047" / "run.py"); E47 = importlib.util.module_from_spec(_e); _e.loader.exec_module(E47)


def cost(u, M):
    return M.kAp * max(u[0], 0) + M.kAm * max(-u[0], 0) + M.kEp * max(u[1], 0) + M.kEm * max(-u[1], 0)


def main():
    P = PR.PRESETS["fixed-income-style"]
    ref = {(tuple(c["start"]), c["cash"], c["unc"], c["costmul"]): c for c in json.load(open(HERE.parent / "048" / "summary.json"))["cells"] if c["regime"] == "fixed-income-style"}
    cells = [((0.0, 0.9), ca, un, cm) for ca in (1.0, 0.005) for un in (1.0, 3.0) for cm in (0.2, 1.0, 5.0)] + [((0.15, 0.0), 1.0, un, cm) for un in (1.0, 3.0) for cm in (0.2, 1.0, 5.0)]
    rows = []; chk = 0.0
    for (st, ca, un, cm), sale in itertools.product(cells, (0.0025, 0.005, 0.01)):
        M = m8_model(bA=1.0, bE=1.0, cE=P["etf_fee"], lam=P["premium"][0], alpha=P["alpha_mean"], premium_sd=P["premium_sd"][0] * un, alpha_sd=P["alpha_sd"] * un,
                     sigma_f=P["factor_sd"][0], sigma_A=P["sigma_A"], gamma=P["gamma"], beta=1.0, etf_rate_buy=P["etf_rate"], etf_rate_sell=sale,
                     fund_rate=P["fund_rate"] * cm, capA=P["fund_cap"], observe_factor=False)
        x0m = np.array(st, float); D = M.solve(x0m, ca, T=2); xd = D["x"][0][0]
        mu0, S0 = M.moments(0, M.m0); xm, em, hm = E47.one_review(M, mu0, S0, x0m, ca)
        hd = ca - np.sum(xd - x0m) - cost(xd - x0m, M)
        if sale == 0.005:
            chk = max(chk, float(np.max(np.abs(xd - np.array(ref[(st, ca, un, cm)]["dynamic"]["x0"])))))
        rows.append(dict(start=st, cash=ca, unc=un, costmul=cm, etf_sale_rate=sale, dE=float(xd[1] - xm[1]), dh=float(hd - hm), dA=float(xd[0] - xm[0]),
                         x_dyn=xd.tolist(), x_my=xm.tolist(), binds=bool(D["h"][0][0] < 1e-6 or min(D["h"][1]) < 1e-6)))
    json.dump(dict(rows=rows, check_vs_048_at_50bp=chk), open(HERE / "sale_rate.json", "w"), indent=1, default=float)
    print(f"check: at the 50 bp sale rate the dynamic root holdings reproduce 048 to {chk:.1e}\n")
    print("| start | cash | prior x | fund rate x | ETF reserve dE at sale 25 / 50 / 100 bp | cash reserve dh at 25 / 50 / 100 bp | fund difference dA at 25 / 50 / 100 bp | one-review ETF at 25 / 50 / 100 bp |")
    print("|---|---|---|---|---|---|---|---|")
    for (st, ca, un, cm) in cells:
        R = sorted([r for r in rows if r["start"] == st and r["cash"] == ca and r["unc"] == un and r["costmul"] == cm], key=lambda r: r["etf_sale_rate"])
        print(f"| {st} | {'slack' if ca == 1.0 else 'tight'} | {un} | {cm} | {' / '.join(f'{r['dE']:+.4f}' for r in R)} | {' / '.join(f'{r['dh']:+.4f}' for r in R)} | {' / '.join(f'{r['dA']:+.4f}' for r in R)} | "
              f"{' / '.join(f'{r['x_my'][1]:.4f}' for r in R)} |")
    print(f"\nlargest |dA| {max(abs(r['dA']) for r in rows):.2f}; runs with |dA| > 1e-5: {sum(abs(r['dA']) > 1e-5 for r in rows)}; dynamic budget binds at {sum(r['binds'] for r in rows)} of {len(rows)} runs")


if __name__ == "__main__":
    main()
