"""Experiment 048 (D18): the dynamic, myopic and exposure-first policies on M8's finite-law variant over the registered
72-cell grid. Registered design: experiments/048-d18-policy-comparison.md.  Run: uv run python experiments/048/run.py
"""
import importlib.util
import itertools
import json
import multiprocessing as mp
import sys
import time
from pathlib import Path

import cvxpy as cp
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "d16-harness"))
from harness import OPT, SCALE, Model  # noqa: E402

_p = importlib.util.spec_from_file_location("presets", HERE.parent / "presets.py"); PR = importlib.util.module_from_spec(_p); _p.loader.exec_module(PR)
_e = importlib.util.spec_from_file_location("run047", HERE.parent / "047" / "run.py"); E47 = importlib.util.module_from_spec(_e); _e.loader.exec_module(E47)
HSLACK = 1e-6
SOLVER_FAIL = []
FALLBACK = []


def model(regime, unc, costmul):
    P = PR.PRESETS[regime]
    lam, am = P["premium"][0], P["alpha_mean"]; lsd, asd = P["premium_sd"][0] * unc, P["alpha_sd"] * unc
    return Model(bA=1.0, bE=1.0, gamma=P["gamma"], beta=1.0, kAp=P["fund_rate"] * costmul, kAm=P["fund_rate"] * costmul,
                 kEp=P["etf_rate"], kEm=P["etf_rate"], capA=P["fund_cap"], cE=P["etf_fee"],
                 theta_atoms=[(lam + a * lsd, am + b * asd) for a in (1, -1) for b in (1, -1)], theta_probs=[0.25] * 4,
                 z_atoms=[(a * P["factor_sd"][0], b * P["sigma_A"], 0.0) for a in (1, -1) for b in (1, -1)], z_probs=[0.25] * 4)


def cost(M, u):
    return float(M.kAp * max(u[0], 0) + M.kAm * max(-u[0], 0) + M.kEp * max(u[1], 0) + M.kEm * max(-u[1], 0))


def score(M, mu, S, x, xm):
    return float(mu @ x - 0.5 * M.gamma * x @ S @ x - cost(M, x - xm))


def one(M, mu, S, xm, hm, fix_fund=False, fibre=None):
    """The one-review problem, optionally with the fund frozen (claim 111's stage 1) or on the fibre p + r a = w (stage 2).
    Returns (x, eta, cash after) or None if infeasible."""
    hm = max(hm, 0.0)                                     # Deviation 1: carried cash of -1e-14 is rounding; clamp at zero
    x = cp.Variable(2); up, dn = cp.Variable(2, nonneg=True), cp.Variable(2, nonneg=True)
    C = M.kAp * up[0] + M.kAm * dn[0] + M.kEp * up[1] + M.kEm * dn[1]
    bc = hm - cp.sum(up - dn) - C >= 0
    cons = [x - xm == up - dn, x >= 0, x[0] <= M.capA, bc]
    if fix_fund:
        cons.append(x[0] == min(xm[0], M.capA))            # Deviation 5 (PM's decision): freeze at the incumbent clipped to the cap
    if fibre is not None:
        cons.append(x[1] + (M.bA / M.bE) * x[0] == fibre)
    pr = cp.Problem(cp.Maximize(SCALE * (mu @ x - 0.5 * M.gamma * cp.quad_form(x, cp.psd_wrap(S)) - C)), cons)
    try:
        pr.solve(solver="CLARABEL", **OPT)
    except cp.error.SolverError:                          # Deviation 1: retry once with default settings, then count
        try:
            pr.solve(solver="CLARABEL")
        except cp.error.SolverError:
            SOLVER_FAIL.append(1); return None
    if pr.status not in ("optimal", "optimal_inaccurate"):
        return None
    xv = np.array(x.value)
    return xv, float(bc.dual_value) / SCALE, float(hm - np.sum(xv - xm) - cost(M, xv - xm))


def stage1_041(M, mu, S):
    """Claim 041's frictionless one-sided stage 1: max G_E(w) over w >= r a with a in the fund box (fees in mu_E)."""
    w, a = cp.Variable(), cp.Variable()
    r = M.bA / M.bE
    cp.Problem(cp.Maximize(SCALE * (mu[1] * w - 0.5 * M.gamma * S[1, 1] * cp.square(w))), [w >= r * a, a >= 0, a <= M.capA]).solve(solver="CLARABEL", **OPT)
    return float(w.value)


def policy_step(M, kind, mu, S, xm, hm):
    """One review of a simple policy; returns (x, eta, cash after, feasible flag)."""
    if kind == "myopic":
        o = one(M, mu, S, xm, hm)
        return (*o, True) if o is not None else (None, None, None, False)
    if kind == "ef111":
        s1 = one(M, mu, S, xm, hm, fix_fund=True)
        if s1 is None:
            return None, None, None, False
        w1 = s1[0][1] + (M.bA / M.bE) * s1[0][0]            # Deviation 6: the exposure at stage 1's frozen fund holding, min(a^-, bar a)
    else:                                                 # ef041
        w1 = stage1_041(M, mu, S)
    nf = len(SOLVER_FAIL)
    o = one(M, mu, S, xm, hm, fibre=w1)
    if o is None and kind == "ef111" and len(SOLVER_FAIL) > nf and hm <= 1e-12 and min(M.kAp + M.kEm, M.kAm + M.kEp) > 0:
        # Deviation 2: with no cash and positive rates, every move along the fibre costs cash, so stage 1's point is the
        # fibre's only feasible point; the solver fails on that one-point set (OSQP confirms the point)
        SOLVER_FAIL.pop(); FALLBACK.append(1)
        return s1[0], s1[1], s1[2], True
    if o is None:
        return None, None, None, False
    return (*o, True)


def evaluate(M, kind, x0m, h0, nodes):
    """Expected two-review objective of a simple policy on the tree; None where a step is infeasible (041's fibre)."""
    mu0, S0 = M.moments(0, M.m0)
    x0, e0, h0p, ok = policy_step(M, kind, mu0, S0, x0m, h0)
    if not ok:
        return dict(feasible=False, where="root")
    val = score(M, mu0, S0, x0, x0m); x1s, e1s, h1s, infeas = [], [], [], 0
    for nd in nodes:
        mu, S = M.moments(1, nd["m"]); xm = x0 * nd["g"]
        x1, e1, h1p, ok = policy_step(M, kind, mu, S, xm, h0p)
        if not ok:
            infeas += 1; x1s.append(None); e1s.append(None); h1s.append(None); continue
        val += M.beta * nd["prob"] * score(M, mu, S, x1, xm); x1s.append(x1); e1s.append(e1); h1s.append(h1p)
    if infeas:
        above = sum(1 for nd in nodes if x0[0] * nd["g"][0] > M.capA + 1e-12)
        return dict(feasible=False, where=f"{infeas} states tomorrow", x0=x0.tolist(), states_fund_above_cap=above)
    q = np.array([nd["prob"] for nd in nodes])
    return dict(feasible=True, value=val, x0=x0.tolist(), x1_mean=(q @ np.array(x1s)).tolist(), eta0=e0, eta1=e1s, h0p=h0p, h1p=h1s,
                binds=bool(h0p < HSLACK or min(h1s) < HSLACK), x1=[x.tolist() for x in x1s])


def incumbent_values(M, x0, x1, eta1, nodes):
    kp, km, cap = np.array([M.kAp, M.kEp]), np.array([M.kAm, M.kEm]), np.array([M.capA, np.inf])
    S = []
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
        S.append(None if None in s else float(M.beta * sum(nd["prob"] * nd["g"][i] * s[k] for k, nd in enumerate(nodes))))
    return S


def cell(args):
    regime, start, cash, unc, costmul = args; t0 = time.time()
    M = model(regime, unc, costmul); x0m = np.array(start, float); h0 = cash
    D = M.solve(x0m, h0, T=2); nodes = D["levels"][1]
    dyn = dict(value=D["value"], x0=D["x"][0][0].tolist(), x1_mean=(np.array([nd["prob"] for nd in nodes]) @ np.array(D["x"][1])).tolist(),
               eta0=D["eta"][0][0], eta1=D["eta"][1], binds=bool(D["h"][0][0] < HSLACK or min(D["h"][1]) < HSLACK))
    out = dict(regime=regime, start=list(start), cash=cash, unc=unc, costmul=costmul, fund_rate=M.kAp, etf_rate=M.kEp, dynamic=dyn)
    for kind in ("myopic", "ef111", "ef041"):
        r = evaluate(M, kind, x0m, h0, nodes)
        if r["feasible"]:
            r["loss_bp"] = 1e4 * (D["value"] - r["value"])
        out[kind] = r
    my = out["myopic"]
    # claim 044 for the myopic policy: its cash prices, incumbent values, residuals and part 3(c)'s existence test
    x1my = [np.array(x) for x in my["x1"]]; e1 = np.array(my["eta1"]); q = np.array([nd["prob"] for nd in nodes])
    Sv = incumbent_values(M, np.array(my["x0"]), x1my, e1, nodes)
    tau, _ = E47.lines_lp(M, x0m, np.array(my["x0"]), my["h0p"], nodes, x1my, my["h1p"])
    out["claim044"] = dict(S_A=Sv[0], S_E=Sv[1], residual_A=None if Sv[0] is None else float(Sv[0] - M.beta * (q @ e1) * (1 + M.kAp)),
                           residual_E=None if Sv[1] is None else float(Sv[1] - M.beta * (q @ e1) * (1 + M.kEp)),
                           E_eta1=float(q @ e1), eta0=my["eta0"], test_passes=bool(tau <= 1e-6), tau=float(tau))
    out["solver_failures"] = len(SOLVER_FAIL); SOLVER_FAIL.clear(); out["fallbacks"] = len(FALLBACK); FALLBACK.clear()
    gaps = [np.max(np.abs(np.array(out["dynamic"]["x0"]) - np.array(my["x0"])))]
    out["myopic_optimal"] = bool(gaps[0] <= 1e-5 and np.max(np.abs(np.array(out["dynamic"]["x1_mean"]) - np.array(my["x1_mean"]))) <= 1e-5)
    out["seconds"] = time.time() - t0
    return out


def main():
    t0 = time.time()
    cells = list(itertools.product(("equity-style", "fixed-income-style"), ((0.0, 0.9), (0.15, 0.0), (0.075, 0.45)), (1.0, 0.005), (1.0, 3.0), (0.2, 1.0, 5.0)))
    with mp.Pool(8) as pool:
        res = pool.map(cell, cells, chunksize=1)
    S = dict(cells=res, seconds=time.time() - t0, model="M8 finite-law variant (model/SPEC.md at main 1e37529)")
    json.dump(S, open(HERE / "summary.json", "w"), separators=(",", ":"), default=lambda o: o.tolist() if hasattr(o, "tolist") else (bool(o) if isinstance(o, np.bool_) else float(o)))
    print("done", len(res), S["seconds"])


if __name__ == "__main__":
    main()
