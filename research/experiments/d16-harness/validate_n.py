"""Validation of harness_n (preparation for experiments 055-056; PM's note 2026-09-30-exp055-056). With one fund, one ETF
and one factor, harness_n reproduces:
  (a) experiment 048's 72 cells (dynamic value and root holdings, from 048's summary.json);
  (b) experiment 054's 144 cells (dynamic and one-review root holdings and values, from 054's summary.json);
  (c) the incumbent values' sign convention: s_1 from the duals equals the finite-difference derivative of the state's
      value in its pre-trade holdings, at a few states, and the root lines of claim 044 hold with them.
It also checks that fund order does not matter with two funds (swapping the funds swaps the solution).
Run: uv run python experiments/d16-harness/validate_n.py
"""
import importlib.util
import itertools
import json
import multiprocessing as mp
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from harness_n import mn_model  # noqa: E402

_p = importlib.util.spec_from_file_location("presets", HERE.parent / "presets.py"); PR = importlib.util.module_from_spec(_p); _p.loader.exec_module(PR)


def one_fund(regime, alpha_sd=None, V=None, fund_rate=None, etf_sell_mult=1.0, premium_sd_mult=1.0):
    P = PR.PRESETS[regime]; fr = P["fund_rate"] if fund_rate is None else fund_rate
    return mn_model(BA=[[1.0]], BE=[[1.0]], lam=P["premium"][0], alpha=P["alpha_mean"], premium_sd=P["premium_sd"][0] * premium_sd_mult,
                    sigma_f=P["factor_sd"][0], sigma_A=P["sigma_A"], alpha_sd=alpha_sd, alpha_revision_var=V, cE=[P["etf_fee"]], gamma=P["gamma"],
                    kp=[fr, P["etf_rate"]], km=[fr, P["etf_rate"] * etf_sell_mult], cap=[P["fund_cap"], np.inf])


def v048(c):
    P = PR.PRESETS[c["regime"]]; un = c["unc"]
    M = one_fund(c["regime"], alpha_sd=P["alpha_sd"] * un, fund_rate=P["fund_rate"] * c["costmul"], premium_sd_mult=un)
    D = M.solve(np.array(c["start"], float), c["cash"])
    return abs(D["value"] - c["dynamic"]["value"]), float(np.max(np.abs(D["x"][0][0] - np.array(c["dynamic"]["x0"]))))


def v054(c):
    P = PR.PRESETS[c["regime"]]; pa = P["alpha_sd"] ** 2; s2 = P["sigma_A"] ** 2
    M = one_fund(c["regime"], V=pa ** 2 / (pa + s2) * c["rv"], etf_sell_mult=c["sell"])
    x0 = np.array(c["start"], float); D = M.solve(x0, c["cash"])
    mu0, S0 = M.moments(0, M.m0); xmy, _, _ = M.one_review(mu0, S0, x0, c["cash"])
    return float(np.max(np.abs(D["x"][0][0] - np.array(c["x_dyn"])))), float(np.max(np.abs(xmy - np.array(c["x_my"]))))


def sign_check():
    """s_1 from the duals against finite differences of the state's one-review value (review 1 is the last review, so the
    state's continuation is its one-review problem from the marked holdings and the root's cash)."""
    worst = 0.0; lines = 0.0
    for regime, x0, h0 in (("fixed-income-style", (0.1, 0.9), 1.0), ("fixed-income-style", (0.15, 0.3), 0.02), ("equity-style", (0.1, 0.5), 0.3)):
        M = one_fund(regime, alpha_sd=PR.PRESETS[regime]["alpha_sd"]); x0 = np.array(x0, float)
        D = M.solve(x0, h0); nodes = D["levels"][1]; xr = D["x"][0][0]; hr = D["h"][0][0]
        for k in (0, 5, 11):
            nd = nodes[k]; mu, S = M.moments(1, nd["m"]); xm = xr * nd["g"]
            def val(xm_):
                x, _, _ = M.one_review(mu, S, xm_, hr); return float(mu @ x - 0.5 * M.gamma * x @ S @ x - M.cost(x - xm_))
            for i in range(2):
                if xm[i] < 1e-4:          # a zero incumbent: the derivative is one-sided and s_1 is not unique there
                    continue
                e = np.zeros(2); e[i] = 1e-5
                fd = (val(xm + e) - val(xm - e)) / 2e-5
                worst = max(worst, abs(fd - D["s"][1][k][i]))
        # claim 044's root line, interior instruments: g_0 + S - eta_hat - (1 + eta_hat) t_0 = 0
        mu0, S0 = M.moments(0, M.m0); g0 = mu0 - M.gamma * S0 @ xr
        q = np.array([nd["prob"] for nd in nodes]); G = np.array([nd["g"] for nd in nodes])
        Sv = M.beta * (q[:, None] * G * np.array(D["s"][1])).sum(0); eh = D["eta"][0][0] + M.beta * q @ np.array(D["eta"][1])
        u = xr - x0
        for i in range(2):
            if xr[i] > 1e-7 and xr[i] < M.cap[i] - 1e-7 and abs(u[i]) > 1e-7:
                t = M.kp[i] if u[i] > 0 else -M.km[i]
                lines = max(lines, abs(g0[i] + Sv[i] - eh - (1 + eh) * t))
    return worst, lines


def order_check():
    P = PR.PRESETS["fixed-income-style"]
    kw = dict(BE=[[1.0]], lam=P["premium"][0], premium_sd=P["premium_sd"][0], sigma_f=P["factor_sd"][0], sigma_A=P["sigma_A"],
              alpha_sd=P["alpha_sd"], gamma=P["gamma"], cap=[0.25, 0.25, np.inf], cE=[0.0])
    A = mn_model(BA=[[1.0], [0.8]], alpha=[0.002, 0.001], kp=[0.002, 0.003, 0.005], km=[0.002, 0.003, 0.005], **kw)
    B = mn_model(BA=[[0.8], [1.0]], alpha=[0.001, 0.002], kp=[0.003, 0.002, 0.005], km=[0.003, 0.002, 0.005], **kw)
    DA = A.solve(np.array([0.1, 0.05, 0.4]), 0.05); DB = B.solve(np.array([0.05, 0.1, 0.4]), 0.05)
    return abs(DA["value"] - DB["value"]), float(np.max(np.abs(DA["x"][0][0][[1, 0, 2]] - DB["x"][0][0])))


def main():
    c48 = json.load(open(HERE.parent / "048" / "summary.json"))["cells"]; c54 = json.load(open(HERE.parent / "054" / "summary.json"))["cells"]
    with mp.Pool(8) as pool:
        r48 = pool.map(v048, c48); r54 = pool.map(v054, c54)
    sc, ln = sign_check(); oc = order_check()
    out = dict(vs048=dict(cells=len(c48), value=max(r[0] for r in r48), x0=max(r[1] for r in r48)),
               vs054=dict(cells=len(c54), x_dyn=max(r[0] for r in r54), x_my=max(r[1] for r in r54)),
               incumbent_duals_vs_fd=sc, root_lines=ln, fund_order=dict(value=oc[0], x0=oc[1]))
    json.dump(out, open(HERE / "validation_n.json", "w"), indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
