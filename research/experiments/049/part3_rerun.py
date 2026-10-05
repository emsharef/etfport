"""Experiment 049, part 3 rerun (PM's note 2026-09-29-exp050-claim112, item 2) against the restated part 3 of claim 046
(math/claim046-d16-bounds-refile at 2c533970; claim 045 refiled). Only the 9 instances where the original part 3's
equation failed for every admissible multiplier are rerun. Run: uv run python experiments/049/part3_rerun.py

The restated test, today's budget binding at the myopic root: an interior purchase of instrument i is consistent iff,
for some admissible tomorrow family and some eta_0 >= 0 that also satisfies the other instrument's root line,
S_i = (eta_0 - eta_0^my + beta E[eta_1])(1 + kappa^+_i), so that S_i >= (beta E[eta_1] - eta_0^my)(1 + kappa^+_i).
Checked two ways:
(i) the inequality: the maximum over the admissible tomorrow set of S_i - (beta E[eta_1] - eta_0^my)(1 + kappa^+_i) >= 0;
(ii) the full statement: the root lines at the myopic root with eta_0 free, with the myopic tomorrow (experiment 047's LP).
"""
import json
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import run as R49  # noqa: E402

E47, E48 = R49.E47, R49.E48
CASES = [("047", 58), ("047", 75), ("047", 84), ("047", 125), ("047", 192),
         ("048", ("equity-style", (0.15, 0.0), 0.005, 3.0, 0.2)), ("048", ("equity-style", (0.15, 0.0), 0.005, 3.0, 1.0)),
         ("048", ("equity-style", (0.15, 0.0), 0.005, 3.0, 5.0)), ("048", ("fixed-income-style", (0.15, 0.0), 0.005, 3.0, 0.2))]


def one(src, key):
    if src == "047":
        M, x0m, h0 = E47.instance(key)
    else:
        rg, st, ca, un, cm = key; M = E48.model(rg, un, cm); x0m, h0 = np.array(st, float), ca
    D = M.solve(x0m, h0, T=2); nodes = D["levels"][1]
    mu0, S0 = M.moments(0, M.m0); xmy, emy0, hmy = E47.one_review(M, mu0, S0, x0m, h0)
    x1my, h1my = [], []
    for nd in nodes:
        mu, S = M.moments(1, nd["m"]); xx, ee, hh = E47.one_review(M, mu, S, xmy * nd["g"], hmy); x1my.append(xx); h1my.append(hh)
    cap = np.array([M.capA, np.inf]); interior = [i for i in range(2) if abs(xmy[i] - x0m[i]) > R49.TOL_X and R49.TOL_X < xmy[i] < cap[i] - R49.TOL_X]
    Lt = R49.LP(M, x0m, xmy, hmy, nodes, x1my, h1my, root=False)
    ineq = []
    for i in interior:
        buy = xmy[i] > x0m[i]; fac = (1 + Lt.kp[i]) if buy else (1 - Lt.km[i])
        c = Lt.S(i) - M.beta * fac * Lt.Eeta1()                    # S_i - beta E[eta_1] fac; the test adds eta_0^my fac
        r = Lt.solve(c=c, tau_cap=R49.TAU, sense=-1)
        mx = float(c @ r.x) + emy0 * fac if r.status == 0 else None
        ineq.append(dict(i=i, buy=bool(buy), max_margin=mx, holds=bool(mx is not None and mx >= -1e-9)))
    tau, _ = E47.lines_lp(M, x0m, xmy, hmy, nodes, x1my, h1my)          # (ii): root lines, eta_0 free when today's budget binds
    opt = bool(np.max(np.abs(xmy - D["x"][0][0])) <= 1e-5)
    return dict(src=src, key=str(key), bind0=bool(hmy < R49.HSLACK), eta0_my=emy0, myopic_optimal=opt, inequality=ineq, full_test_tau=float(tau),
                full_test_passes=bool(tau <= 1e-6))


def main():
    out = [one(s, k) for s, k in CASES]
    json.dump(dict(cases=out, statement="claim 046 part 3 at 2c533970 (math/claim046-d16-bounds-refile)"), open(HERE / "part3_rerun.json", "w"), indent=1, default=float)
    for r in out:
        print(r["src"], r["key"], "bind0", r["bind0"], "eta0_my %.2e" % r["eta0_my"], "myopic optimal", r["myopic_optimal"],
              "inequality", [(q["i"], q["holds"], None if q["max_margin"] is None else round(q["max_margin"], 7)) for q in r["inequality"]],
              "full test", r["full_test_passes"])


if __name__ == "__main__":
    main()
