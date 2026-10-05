"""Experiment 052: claim 047 (D19's reserve rule; math/claim047-d19-reserve-rule at 5b6373ae) against the exact two-review
program. Registered design: experiments/052-claim047-reserve-rule-check.md.  Run: uv run python experiments/052/run.py
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
from harness import m8_model  # noqa: E402,F401

_n = importlib.util.spec_from_file_location("run049", HERE.parent / "049" / "run.py"); R49 = importlib.util.module_from_spec(_n); _n.loader.exec_module(R49)
E47, E48 = R49.E47, R49.E48
TOLX, HS = 1e-7, 1e-6


def need_parts(M, nodes, x0):
    kp = np.array([M.kAp, M.kEp]); out = []
    for nd in nodes:
        mu, S = M.moments(1, nd["m"])
        xhat = np.maximum(mu - kp, 0) / (M.gamma * np.diag(S))
        n = float(np.sum((1 + kp) * np.maximum(xhat - nd["g"] * x0, 0)))
        eb = float(max(np.maximum(mu - kp, 0) / (1 + kp)))
        out.append(dict(need=n, eta_bar=eb, mu=mu, S=S, xhat=xhat))
    return out


def ranges(L, c):
    lo = L.solve(c=c, tau_cap=R49.TAU, sense=1); hi = L.solve(c=c, tau_cap=R49.TAU, sense=-1)
    return (float(c @ lo.x) if lo.status == 0 else None, float(c @ hi.x) if hi.status == 0 else None)


def slope_today(M, x, xm, i, g0i):
    """The ETF's (or fund's) cost slope today at x: kappa^+ if bought, -kappa^- if sold, the held marginal if held inside."""
    kp = (M.kAp, M.kEp)[i]; km = (M.kAm, M.kEm)[i]
    u = x[i] - xm[i]
    return kp if u > TOLX else (-km if u < -TOLX else None)


def check(M, x0m, h0, tag):
    rec = dict(tag=tag)
    D = M.solve(x0m, h0, T=2); nodes = D["levels"][1]; xd = D["x"][0][0]; x1 = D["x"][1]; hd = D["h"][0][0]; h1 = D["h"][1]
    mu0, S0 = M.moments(0, M.m0); xmy, emy0, hmy = E47.one_review(M, mu0, S0, x0m, h0)
    q = np.array([nd["prob"] for nd in nodes]); G = np.array([nd["g"] for nd in nodes])
    x1my, h1my = [], []
    for nd in nodes:
        mu, S = M.moments(1, nd["m"]); xx, ee, hh = E47.one_review(M, mu, S, xmy * nd["g"], hmy); x1my.append(xx); h1my.append(hh)
    Ld = R49.LP(M, x0m, xd, hd, nodes, x1, h1, root=False)
    # part 2(a): ETF idle tomorrow in every state at the dynamic optimum
    idle = all(abs(x1[k][1] - xd[1] * nd["g"][1]) <= TOLX for k, nd in enumerate(nodes))
    if idle:
        SE = ranges(Ld, Ld.S(1))
        rec["p2a"] = dict(S_E_range=SE, zero_in_range=(bool(SE[0] <= 1e-9 and SE[1] >= -1e-9) if None not in SE else None),
                          reserve_E=float(xd[1] - xmy[1]), today_slack=bool(hd > HS),
                          etf_interior_tomorrow=bool(all(x1[k][1] > TOLX for k in range(len(nodes)))))
    # part 2(b) at the dynamic root, and the certificate
    Pd = need_parts(M, nodes, xd); Nd = max(p["need"] for p in Pd)
    if hd > HS and hd >= Nd:
        r = Ld.solve(extra_bounds={Ld.e1(k): (None, 0.0) for k in range(Ld.K)})
        rec["p2b"] = dict(feasible=bool(r.status == 0 and r.fun <= 1e-6), tau=float(r.fun) if r.status == 0 else None)
    Xs = M.solve(x0m, h0, T=2, budget_t={0}); xs = Xs["x"][0][0]; hs = Xs["h"][0][0]
    Ps = need_parts(M, nodes, xs); Ns = max(p["need"] for p in Ps)
    if hs > HS and hs >= Ns:
        rec["cert"] = dict(equal=bool(np.max(np.abs(xs - xd)) <= 1e-5), gap=float(np.max(np.abs(xs - xd))))
    # the displayed bound on N(x^my) in the inputs
    Pm = need_parts(M, nodes, xmy); Nm = max(p["need"] for p in Pm)
    eps = np.array([nd["m"] - M.m0 for nd in nodes]); el, ea = eps[:, 0].max(), eps[:, 1].max()
    S1 = M.moments(1, nodes[0]["m"])[1]; gmin = G.min(0)
    rhs = ((1 + M.kAp) * max(max(mu0[0] + M.bA * el + ea - M.kAp, 0) / (M.gamma * S1[0, 0]) - gmin[0] * xmy[0], 0)
           + (1 + M.kEp) * max(max(mu0[1] + M.bE * el - M.kEp, 0) / (M.gamma * S1[1, 1]) - gmin[1] * xmy[1], 0))
    rec["Nbound"] = dict(N=Nm, rhs=float(rhs), ok=bool(Nm <= rhs + 1e-9))
    # the budget channel's bounds at the dynamic root (finite law), with h > 0
    if hd > HS:
        U = [p["need"] > hd for p in Pd]
        ce = M.beta * Ld.Eeta1(); up = ranges(Ld, ce)[1]
        bnd = float(M.beta * sum(q[k] * Pd[k]["eta_bar"] for k in range(len(nodes)) if U[k]))
        # S_i: with eta_1 = 0 in the covered states (admissible there by claim 046 1(b)), the uncovered part's maximum
        ext = {Ld.e1(k): (None, 0.0) for k in range(Ld.K) if not U[k]}
        sb = []
        for i in range(2):
            cU = np.zeros(Ld.n)
            for k in range(Ld.K):
                if U[k]:
                    cU[Ld.e1(k)] += M.beta * q[k] * G[k, i]; cU[Ld.s1(k, i)] += M.beta * q[k] * G[k, i]
            r = Ld.solve(c=cU, extra_bounds=ext, tau_cap=R49.TAU, sense=-1)
            kp = (M.kAp, M.kEp)[i]
            tb = M.beta * sum(q[k] * G[k, i] * (Pd[k]["eta_bar"] + (1 + Pd[k]["eta_bar"]) * kp) for k in range(Ld.K) if U[k])
            sb.append(float(cU @ r.x) - tb if r.status == 0 else None)
        rec["budget"] = dict(Eeta1_max=up, bound=bnd, ok=bool(up is not None and up <= bnd + 1e-9), S_excess=sb, U=int(sum(U)))
    # part 3(a): Pi_E at the myopic root (its tomorrow), sign against p^fix - p^my
    if hmy > HS and xmy[1] > TOLX and xmy[0] > TOLX:
        Lm = R49.LP(M, x0m, xmy, hmy, nodes, x1my, h1my, root=False)
        t0 = slope_today(M, xmy, x0m, 1, None)
        if t0 is not None:
            cPi = Lm.S(1) - M.beta * (1 + t0) * Lm.Eeta1(); rng = ranges(Lm, cPi)
            F = M.solve(x0m, h0, T=2, fix_root_fund=float(xmy[0])); pf = F["x"][0][0][1]
            if None not in rng and (rng[0] > 1e-9 or rng[1] < -1e-9) and abs(pf - xmy[1]) > 1e-5:
                rec["p3a"] = dict(Pi_range=rng, move=float(pf - xmy[1]), ok=bool(np.sign(pf - xmy[1]) == (1 if rng[0] > 1e-9 else -1)))
    # part 3(b): slack budgets, fund fixed at a^my, ETF interior at both
    F = M.solve(x0m, h0, T=2, fix_root_fund=float(xmy[0])); xf = F["x"][0][0]; hf = F["h"][0][0]
    slack_all = bool(hmy > HS and hf > HS and min(F["h"][1]) > HS and min(h1my) > HS)
    if slack_all and xmy[1] > TOLX and xf[1] > TOLX:
        Lf = R49.LP(M, x0m, xf, hf, nodes, F["x"][1], F["h"][1], root=False)
        SE = ranges(Lf, Lf.S(1))
        g0f = (mu0 - M.gamma * S0 @ xf)[1]; g0m = (mu0 - M.gamma * S0 @ xmy)[1]
        tm = g0m if abs(xmy[1] - x0m[1]) <= TOLX else slope_today(M, xmy, x0m, 1, None)
        tf_same = slope_today(M, xf, x0m, 1, None); tm_same = slope_today(M, xmy, x0m, 1, None)
        # identity with the fixed point's own slope: t^fix = g_0E(x^fix) + S_E (its root line), for the S_E attained
        dp = xf[1] - xmy[1]; see = M.gamma * S0[1, 1]
        same = tf_same is not None and tm_same is not None and tf_same == tm_same
        bound = (M.beta * max(M.kEp, M.kEm) * float(q @ G[:, 1]) + M.kEp + M.kEm) / see
        if None in SE:
            rec["p3b_lp_infeasible"] = True
            same = None
        rec["p3b"] = dict(dp=float(dp), SE_range=SE, same_direction=bool(same),
                          same_formula_err=float(min(abs(dp - SE[0] / see), abs(dp - SE[1] / see))) if same else None,
                          within_SE_range=bool(same and SE[0] / see - 1e-6 <= dp <= SE[1] / see + 1e-6) if same else None,
                          bound=float(bound), bound_ok=bool(abs(dp) <= bound + 1e-9))
    # part 4: the need's slopes, by central differences on need(z'), at states with an active interior fund purchase
    sl = []
    for k, nd in enumerate(nodes):
        p = Pm[k]
        if p["mu"][0] - M.kAp > 1e-6 and p["xhat"][0] - nd["g"][0] * xmy[0] > 1e-6:
            d = 1e-7
            f = lambda da: (1 + M.kAp) * max(max(p["mu"][0] + da - M.kAp, 0) / (M.gamma * p["S"][0, 0]) - nd["g"][0] * xmy[0], 0)
            num = (f(d) - f(-d)) / (2 * d); form = (1 + M.kAp) / (M.gamma * p["S"][0, 0])
            fk = lambda dk: (1 + M.kAp + dk) * max(max(p["mu"][0] - M.kAp - dk, 0) / (M.gamma * p["S"][0, 0]) - nd["g"][0] * xmy[0], 0)
            numk = (fk(d) - fk(-d)) / (2 * d); formk = (p["xhat"][0] - nd["g"][0] * xmy[0]) - (1 + M.kAp) / (M.gamma * p["S"][0, 0])
            sl.append(max(abs(num - form) / abs(form), abs(numk - formk) / max(abs(formk), 1e-12)))
    rec["p4_rel_err"] = max(sl) if sl else None
    # part 5: some state prices cash for every admissible family at the dynamic optimum
    Ljoint = R49.LP(M, x0m, xd, hd, nodes, x1, h1, root=True)
    c = np.zeros(Ljoint.n)
    for k in range(Ljoint.K):
        c[Ljoint.e1(k)] = 1.0
    r = Ljoint.solve(c=c, tau_cap=R49.TAU, sense=1)
    if r.status == 0 and float(c @ r.x) > 1e-7:
        rec["p5"] = dict(h=hd, N=Nd, ok=bool(hd <= Nd + 1e-9 and (hd <= HS or hd < Nd)))
    return rec


def run_main(i):
    M, x0m, h0 = E47.instance(i); return check(M, x0m, h0, f"047 main {i}")


def run_cell(args):
    rg, st, ca, un, cm = args; M = E48.model(rg, un, cm); return check(M, np.array(st, float), ca, f"048 {args}")


def main():
    cells = list(itertools.product(("equity-style", "fixed-income-style"), ((0.0, 0.9), (0.15, 0.0), (0.075, 0.45)), (1.0, 0.005), (1.0, 3.0), (0.2, 1.0, 5.0)))
    with mp.Pool(8) as pool:
        a = pool.map(run_main, range(300), chunksize=4)
        b = pool.map(run_cell, cells, chunksize=2)
    json.dump(dict(main047=a, cells048=b, statement="claim 047 at 5b6373ae (math/claim047-d19-reserve-rule)"), open(HERE / "summary.json", "w"), indent=0,
              default=lambda o: o.tolist() if hasattr(o, "tolist") else float(o))
    print("done")


if __name__ == "__main__":
    main()
