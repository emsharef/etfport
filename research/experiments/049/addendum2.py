"""Experiment 049, addendum 2 (PM's note 2026-09-29-exp049-close-gaps).
(1) Claim 046 at its current head against the text checked (claim 045, 919441d4): among parts 1, 2 and 4 only 1(c)
    changed. It is rerun on experiment 049's instances (047's 300 main, 048's 72 cells). In the joint multiplier family
    (today's lines included), eta_1(z') <= eta_bar(z') in every state that buys some instrument or has slack cash; and,
    where no state holds everything with all cash spent, eta_0 <= eta_hat_0 <= eta_0 + beta E[eta_bar] over the joint set.
(2) Part 3's slack-today equation, by a targeted search. Instances with today's budget slack at the myopic root, the
    myopic root trading instrument i strictly inside its box, and some state tomorrow trading i:
    - A: all cash slack (h^-_0 = 1);
    - B: today slack but tight (h^-_0 = the myopic root's spend + 1e-3, so tomorrow can bind);
    - C: a costless ETF with h^-_0 = 1 (the identity case).
    Tested: "the equation S_i = beta E[eta_1](1 + kappa^+_i) (sale: 1 - kappa^-_i) holds for some admissible tomorrow
    family", against myopic optimality (holdings within 1e-5, experiment 047's rule).
Run: uv run python experiments/049/addendum2.py
"""
import itertools
import json
import multiprocessing as mp
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import run as R49  # noqa: E402

E47, E48 = R49.E47, R49.E48


def p1c(M, x0m, h0):
    D = M.solve(x0m, h0, T=2); nodes = D["levels"][1]; x0 = D["x"][0][0]; x1 = D["x"][1]; h0p = D["h"][0][0]; h1p = D["h"][1]
    eb, _ = R49.eta_bar_need(M, nodes, x0, h0p)
    L = R49.LP(M, x0m, x0, h0p, nodes, x1, h1p, root=True)
    buys = [bool(np.any(x1[k] - x0 * nd["g"] > R49.TOL_X)) for k, nd in enumerate(nodes)]
    slack = [h1p[k] > R49.HSLACK for k in range(len(nodes))]
    held_spent = [not buys[k] and not np.any(x1[k] - x0 * nd["g"] < -R49.TOL_X) and not slack[k] for k, nd in enumerate(nodes)]
    viol = []
    for k in range(len(nodes)):
        if buys[k] or slack[k]:
            c = np.zeros(L.n); c[L.e1(k)] = 1
            r = L.solve(c=c, tau_cap=R49.TAU, sense=-1)
            if r.status == 0:
                viol.append(float(r.x[L.e1(k)] - eb[k]))
    rec = dict(max_eta1_minus_bar=max(viol) if viol else None, any_held_spent=bool(any(held_spent)))
    if not any(held_spent):
        ce = np.zeros(L.n); ce[L.e0] = -1
        for k in range(len(nodes)):
            ce[L.e1(k)] += M.beta * L.q[k]                     # eta_hat_0 - eta_0 = beta E[eta_1]
        lo = L.solve(c=ce, tau_cap=R49.TAU, sense=1); hi = L.solve(c=ce, tau_cap=R49.TAU, sense=-1)
        ce_full = ce.copy(); ce_full[L.e0] += 1
        rec.update(min_gap=float(ce @ lo.x) + float(lo.x[L.e0]) if lo.status == 0 else None,
                   max_over=float(ce @ hi.x) + float(hi.x[L.e0]) - M.beta * L.q @ eb if hi.status == 0 else None)
    return rec


def part3_slack(args):
    fam, i = args
    M, x0m, h0 = E47.instance(i, costless=(fam == "C"))
    mu0, S0 = M.moments(0, M.m0)
    if fam in ("A", "C"):
        h0 = 1.0
    else:
        x_, e_, hleft = E47.one_review(M, mu0, S0, x0m, 1.0); spend = 1.0 - hleft
        h0 = max(spend, 0.0) + 1e-3
    D = M.solve(x0m, h0, T=2); nodes = D["levels"][1]
    xmy, emy0, hmy = E47.one_review(M, mu0, S0, x0m, h0)
    if hmy <= R49.HSLACK:
        return dict(fam=fam, i=i, eligible=False, why="today binds")
    cap = np.array([M.capA, np.inf])
    x1my, h1my = [], []
    for nd in nodes:
        mu, S = M.moments(1, nd["m"]); xx, ee, hh = E47.one_review(M, mu, S, xmy * nd["g"], hmy); x1my.append(xx); h1my.append(hh)
    out = []
    for j in range(2):
        if not (abs(xmy[j] - x0m[j]) > R49.TOL_X and R49.TOL_X < xmy[j] < cap[j] - R49.TOL_X):
            continue
        trades_tom = any(abs(x1my[k][j] - xmy[j] * nd["g"][j]) > R49.TOL_X for k, nd in enumerate(nodes))
        if not trades_tom:
            continue
        L = R49.LP(M, x0m, xmy, hmy, nodes, x1my, h1my, root=False)
        buy = xmy[j] > x0m[j]; fac = (1 + L.kp[j]) if buy else (1 - L.km[j])
        c = L.S(j) - M.beta * fac * L.Eeta1()
        lo = L.solve(c=c, tau_cap=R49.TAU, sense=1); hi = L.solve(c=c, tau_cap=R49.TAU, sense=-1)
        rng = (float(c @ lo.x), float(c @ hi.x)) if lo.status == 0 and hi.status == 0 else (None, None)
        out.append(dict(j=j, buy=bool(buy), range=rng, holds=bool(rng[0] is not None and rng[0] <= 1e-9 and rng[1] >= -1e-9),
                        costless_both=bool(L.kp[j] == 0 and L.km[j] == 0), tom_slack_all=bool(min(h1my) > R49.HSLACK)))
    if not out:
        return dict(fam=fam, i=i, eligible=False, why="no interior trade traded again tomorrow")
    opt = bool(np.max(np.abs(xmy - D["x"][0][0])) <= 1e-5)
    tau, _ = E47.lines_lp(M, x0m, xmy, hmy, nodes, x1my, h1my)
    return dict(fam=fam, i=i, eligible=True, myopic_optimal=opt, full_test=bool(tau <= 1e-6), eqs=out)


def main():
    cells = list(itertools.product(("equity-style", "fixed-income-style"), ((0.0, 0.9), (0.15, 0.0), (0.075, 0.45)), (1.0, 0.005), (1.0, 3.0), (0.2, 1.0, 5.0)))
    with mp.Pool(8) as pool:
        a = pool.map(p1c_main, range(300), chunksize=4)
        b = pool.map(p1c_cell, cells, chunksize=2)
        s = pool.map(part3_slack, [(f, i) for f in ("A", "B", "C") for i in range(300)], chunksize=4)
    json.dump(dict(p1c_main=a, p1c_cells=b, part3_slack=s, statement="claim 046 at math/claim046-d16-bounds-refile 531649b4 against claim 045 at 919441d4"),
              open(HERE / "addendum2.json", "w"), indent=0, default=lambda o: o.tolist() if hasattr(o, "tolist") else float(o))
    print("done")


def p1c_main(i):
    M, x0m, h0 = E47.instance(i); r = p1c(M, x0m, h0); r["tag"] = f"047 main {i}"; return r


def p1c_cell(args):
    rg, st, ca, un, cm = args; M = E48.model(rg, un, cm); r = p1c(M, np.array(st, float), ca); r["tag"] = f"048 {args}"; return r


if __name__ == "__main__":
    main()
