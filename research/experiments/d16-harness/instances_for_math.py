"""Instances for math (D16; math's note 2026-09-29-d16-instances-wanted): cells where the dynamic and the one-review
root decisions differ under a binding budget, as instances without conclusions (rule 22). Not an experiment.
Run: uv run python experiments/d16-harness/instances_for_math.py  (writes instances_for_math.json)

Regimes: experiments/presets.py mapped to one fund and one ETF (the market factor only: premium 1.5% +- 0.5%, factor SD 8%;
b_A = b_E = 1; the fund's alpha law +- its prior SD; residual SD 2%; the presets' fund and ETF rates, fund cap 0.25,
gamma 5, beta 1; no fee). Start: the presets' "mixed" start (fund 0.075, ETF 0.45 of wealth), with cash the scanned tight
level. Per instance: the inputs, both root holdings, the dynamic program's cash prices by state tomorrow, the incumbent
values S_A and S_E, and the residual S_A - beta E[eta_1](1 + kappa^+_A), computed both from the dynamic program's own
tomorrow and from the myopic policy's tomorrow (claim 044 part 3(c) uses the latter).
"""
import importlib.util
import json
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from harness import Model  # noqa: E402

_p = importlib.util.spec_from_file_location("presets", HERE.parent / "presets.py"); PR = importlib.util.module_from_spec(_p); _p.loader.exec_module(PR)
_e = importlib.util.spec_from_file_location("run047", HERE.parent / "047" / "run.py"); E47 = importlib.util.module_from_spec(_e); _e.loader.exec_module(E47)


def model(name):
    P = PR.PRESETS[name]
    lam, lsd, am, asd = P["premium"][0], P["premium_sd"][0], P["alpha_mean"], P["alpha_sd"]
    return Model(bA=1.0, bE=1.0, gamma=P["gamma"], beta=1.0, kAp=P["fund_rate"], kAm=P["fund_rate"], kEp=P["etf_rate"], kEm=P["etf_rate"],
                 capA=P["fund_cap"], cE=P["etf_fee"],
                 theta_atoms=[(lam + a * lsd, am + b * asd) for a in (1, -1) for b in (1, -1)], theta_probs=[0.25] * 4,
                 z_atoms=[(a * P["factor_sd"][0], b * P["sigma_A"], 0.0) for a in (1, -1) for b in (1, -1)], z_probs=[0.25] * 4)


def incumbent_values(M, x0, x1, eta1, nodes):
    """S_i = beta E[g_i s_i], s_i from tomorrow's regime (held inside the box: its marginal; bought/sold: the scaled
    threshold); None where some state holds i at a box bound (s_i not pinned)."""
    kp, km, cap = np.array([M.kAp, M.kEp]), np.array([M.kAm, M.kEm]), np.array([M.capA, np.inf])
    q = np.array([nd["prob"] for nd in nodes]); S = []
    for i in range(2):
        s = []
        for k, nd in enumerate(nodes):
            mu, Sg = M.moments(1, nd["m"]); g1 = (mu - M.gamma * Sg @ x1[k])[i]; u = x1[k][i] - x0[i] * nd["g"][i]
            if u > 1e-7:
                s.append(eta1[k] + (1 + eta1[k]) * kp[i])
            elif u < -1e-7:
                s.append(eta1[k] - (1 + eta1[k]) * km[i])
            elif 1e-7 < x1[k][i] < cap[i] - 1e-7:
                s.append(g1)
            else:
                s.append(None)
        S.append(None if None in s else float(M.beta * sum(q[k] * nodes[k]["g"][i] * s[k] for k in range(len(nodes)))))
    return S


def record(name, M, x0m, h0):
    D = M.solve(x0m, h0, T=2); nodes = D["levels"][1]; x0 = D["x"][0][0]; eta1 = np.array(D["eta"][1])
    mu0, S0 = M.moments(0, M.m0)
    xmy, emy0, hmy = E47.one_review(M, mu0, S0, x0m, h0)
    x1my, e1my = [], []
    for nd in nodes:
        mu, S = M.moments(1, nd["m"]); xx, ee, _ = E47.one_review(M, mu, S, xmy * nd["g"], hmy); x1my.append(xx); e1my.append(ee)
    e1my = np.array(e1my); q = np.array([nd["prob"] for nd in nodes])
    Sd = incumbent_values(M, x0, D["x"][1], eta1, nodes); Sm = incumbent_values(M, xmy, x1my, e1my, nodes)
    res = lambda S, e: (None if S[0] is None else float(S[0] - M.beta * (q @ e) * (1 + M.kAp)))
    resE = lambda S, e: (None if S[1] is None else float(S[1] - M.beta * (q @ e) * (1 + M.kEp)))
    return dict(regime=name, inputs=dict(b_A=M.bA, b_E=M.bE, gamma=M.gamma, beta=M.beta, fund_rates=[M.kAp, M.kAm], etf_rates=[M.kEp, M.kEm],
                                         fund_cap=M.capA, theta_atoms=M.theta_atoms, z_atoms=M.z_atoms, start=x0m.tolist(), cash=h0),
                root_dynamic=x0.tolist(), root_one_review=xmy.tolist(), cash_after_root=dict(dynamic=D["h"][0][0], one_review=hmy),
                eta0=dict(dynamic=D["eta"][0][0], one_review=emy0),
                eta1_by_state=dict(dynamic=eta1.tolist(), one_review=e1my.tolist(), state_prob=q.tolist(), state_gross_returns=[nd["g"].tolist() for nd in nodes]),
                S_dynamic=dict(S_A=Sd[0], S_E=Sd[1], residual_A=res(Sd, eta1), residual_E=resE(Sd, eta1)),
                S_one_review_tomorrow=dict(S_A=Sm[0], S_E=Sm[1], residual_A=res(Sm, e1my), residual_E=resE(Sm, e1my)),
                differ=float(np.max(np.abs(x0 - xmy))))


def main():
    """The presets' cells: at the mixed start the budget never binds (the ETF starts above its target and is sold),
    so the scan covers the presets' all-fund, empty and part-ETF starts at tight cash; the cells where the two root
    decisions differ under a binding budget are kept. Then four of experiment 047's instances (assumed ranges, seed
    (2047, 0, i)) where the one-review root buys the fund inside its box under a binding budget."""
    out = []
    for name in ("equity-style", "fixed-income-style"):
        M = model(name)
        for start in ((0.075, 0.45), (0.15, 0.0), (0.0, 0.0), (0.0, 0.2)):
            for h0 in (0.02, 0.05, 0.1, 0.2):
                r = record(name, M, np.array(start), h0)
                if r["differ"] > 1e-5 and (r["eta0"]["dynamic"] > 1e-7 or max(r["eta1_by_state"]["dynamic"]) > 1e-7):
                    out.append(r)
    for i in (56, 233, 274, 106):
        M, x0m, h0 = E47.instance(i)
        r = record(f"experiment 047 main instance {i} (assumed ranges)", M, x0m, h0); out.append(r)
    json.dump(out, open(HERE / "instances_for_math.json", "w"), indent=1, default=float)
    for r in out:
        print(r["regime"], "start", r["inputs"]["start"], "cash", round(r["inputs"]["cash"], 4), "dyn", np.round(r["root_dynamic"], 4), "my", np.round(r["root_one_review"], 4),
              "eta0", round(r["eta0"]["dynamic"], 5), "E eta1", round(float(np.dot(r["eta1_by_state"]["state_prob"], r["eta1_by_state"]["dynamic"])), 5),
              "resid A/E (my tomorrow)", r["S_one_review_tomorrow"]["residual_A"], r["S_one_review_tomorrow"]["residual_E"])

if __name__ == "__main__":
    main()
