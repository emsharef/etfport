"""Experiment 054 (D21 confirmation): claim 047 part 3(b)'s literal rule (053's rule_band, reused unchanged) against the
dynamic optimum and the repeated one-review policy on 144 new cells. Registered design:
experiments/054-d21-literal-rule-confirmation.md.  Run: uv run python experiments/054/run.py
"""
import importlib.util
import itertools
import json
import multiprocessing as mp
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "d16-harness"))
from harness import m8_model  # noqa: E402

_s = importlib.util.spec_from_file_location("run053", HERE.parent / "053" / "run.py"); R53 = importlib.util.module_from_spec(_s); _s.loader.exec_module(R53)
PR, E47 = R53.PR, R53.E47
HS, TOLG = 1e-6, 1e-5
STARTS = [(0.05, 0.10), (0.05, 0.80), (0.22, 0.30), (0.10, 0.50)]
CASH = [0.30, 0.02]
RV = [0.5, 2.0, 8.0]
SELL = [0.75, 1.5, 3.0]


def model(regime, rv, sell):
    """053's model with the revision-variance and ETF-sale-rate multipliers set together."""
    P = PR.PRESETS[regime]
    pa = P["alpha_sd"] ** 2; s2 = P["sigma_A"] ** 2; V = pa ** 2 / (pa + s2) * rv
    return m8_model(bA=1.0, bE=1.0, cE=P["etf_fee"], lam=P["premium"][0], alpha=P["alpha_mean"], premium_sd=P["premium_sd"][0], alpha_revision_var=V,
                    sigma_f=P["factor_sd"][0], sigma_A=P["sigma_A"], gamma=P["gamma"], beta=1.0,
                    etf_rate_buy=P["etf_rate"], etf_rate_sell=P["etf_rate"] * sell,
                    fund_rate_buy=P["fund_rate"], fund_rate_sell=P["fund_rate"], fund_rate=P["fund_rate"],
                    capA=P["fund_cap"], observe_factor=False)


def cell(args):
    regime, start, cash, rv, sell = args
    M = model(regime, rv, sell); x0m = np.array(start, float)
    D = M.solve(x0m, cash, T=2); nodes = D["levels"][1]; xd = D["x"][0][0]; hd = R53.cash_after(M, cash, xd, x0m)
    mu0, S0 = M.moments(0, M.m0); xmy, emy, hmy = E47.one_review(M, mu0, S0, x0m, cash)
    xs_my, _ = R53.tomorrow(M, nodes, xmy, hmy); v_my = R53.value(M, nodes, x0m, xmy, xs_my)
    xr, SE, it = R53.rule_band(M, nodes, x0m, cash, xmy); hr = R53.cash_after(M, cash, xr, x0m)
    clipped = bool(hr < 1e-9 and abs(xr[1] - xmy[1]) > 1e-9)       # the budget clip leaves the cash at zero, short of the line
    xs_r, _ = R53.tomorrow(M, nodes, xr, hr); v_r = R53.value(M, nodes, x0m, xr, xs_r)
    Lmy, Lr = 1e4 * (D["value"] - v_my), 1e4 * (D["value"] - v_r)
    binds = bool(D["h"][0][0] < HS or min(D["h"][1]) < HS)
    fund_gap = float(abs(xmy[0] - xd[0])); etf_gap = float(abs(xr[1] - xd[1]))
    return dict(regime=regime, start=list(start), cash=cash, rv=rv, sell=sell, etf_sell=M.kEm,
                x_dyn=xd.tolist(), x_my=xmy.tolist(), x_rule=xr.tolist(), S_E=SE, iters=it, converged=bool(it < 60), clipped=clipped,
                reserve_dyn=[float(xd[1] - xmy[1]), float(hd - hmy)], reserve_rule=[float(xr[1] - xmy[1]), float(hr - hmy)],
                loss_my_bp=Lmy, loss_rule_bp=Lr, recovery=(1 - Lr / Lmy) if Lmy > 0.01 else None,
                dyn_binds=binds, fund_gap=fund_gap, etf_gap=etf_gap, in_domain=bool(not binds and fund_gap <= TOLG),
                math=R53.math_fields(M, x0m, cash, D, xmy, hmy))


def main():
    cells = list(itertools.product(("equity-style", "fixed-income-style"), STARTS, CASH, RV, SELL))
    with mp.Pool(8) as pool:
        res = pool.map(cell, cells, chunksize=2)
    json.dump(dict(cells=res, statement="claim 047 at affb08d4 (part 3(b) applied literally; 053's rule_band)"), open(HERE / "summary.json", "w"), indent=0,
              default=lambda o: o.tolist() if hasattr(o, "tolist") else float(o))
    print("done", len(res))


if __name__ == "__main__":
    main()
