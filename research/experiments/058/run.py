"""Experiment 058 (D26): the integrated M9 example; three policies; losses against claims 049's and 115's bound terms on the
registered sensitivity design; the worked example under the product law; the larger menu.
Registered design: experiments/058-d26-integrated-example.md. Definitions: math's and mathb's notes of 2026-10-01.
Run: uv run python experiments/058/run.py [design|worked|larger|all]   (writes summary_<part>.json)
"""
import itertools
import json
import multiprocessing as mp
import platform
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "d26-prep")); sys.path.insert(0, str(HERE.parent / "d16-harness"))
import policies as P  # noqa: E402
import spec  # noqa: E402

SETTINGS = [("base", {}), ("pred_alpha+0.004", dict(pred_alpha=0.004)), ("pred_alpha-0.004", dict(pred_alpha=-0.004)),
            ("pred_lambda+0.005", dict(pred_lambda=0.005)), ("pred_lambda-0.005", dict(pred_lambda=-0.005)),
            ("unc x0.25", dict(unc=0.25)), ("unc x4", dict(unc=4.0)), ("pred_alpha+0.004 unc x4", dict(pred_alpha=0.004, unc=4.0)),
            ("pred_alpha+0.008", dict(pred_alpha=0.008)), ("q_alpha 1e-6", dict(q_alpha=1e-6)),
            ("fund rates x2", dict(fund_mult=2.0)), ("ETF rates x4", dict(etf_mult=4.0)), ("ETF rates x0.25", dict(etf_mult=0.25))]
REGIMES = ("equity-style", "fixed-income-style")
LEVELS = (0.0, 0.05, 0.10)


def var_level(q, Y, eps):
    """VaR_{1-eps}(Y): the smallest v with P(Y <= v) >= 1 - eps (mathb's var_level)."""
    o = np.argsort(Y); c = np.cumsum(q[o])
    return float(Y[o][np.searchsorted(c, 1 - eps - 1e-12)])


def evaluate(M, x0m, h0, detail=False):
    t = {}; t0 = time.time()
    R = P.policies(M, x0m, h0); t["policies_total"] = time.time() - t0
    t["dynamic_solver"] = R["stats"]["dynamic"]["solve_time"]; t["plan_solver"] = R["stats"]["plan"]["solve_time"]
    nodes = R["nodes"]; q = np.array([nd["prob"] for nd in nodes]); W0 = R["W0"]; bp = lambda v: 1e4 * v / W0
    D = R["D"]; out = dict(W0=W0, states=len(nodes), min_gross=float(min(nd["g"].min() for nd in nodes)), in_scope=spec.entrywise_nonnegative(M),
                           V=R["V"], status=R["stats"])
    out["dynamic_eta0"] = D["eta"][0][0]; e1 = np.array(D["eta"][1]); out["dynamic_E_eta1"] = float(q @ e1); out["dynamic_tomorrow_binding_states"] = int(np.sum(e1 > 1e-8))
    acc = dict(J_dyn_minus_V=R["dynamic"]["J"] - R["V"])
    for name in ("myopic", "plan", "dynamic"):
        r = R[name]; x = r["x"]; tm = r["tomorrow"]
        cost0 = P.cost(M, x - x0m); cost1 = float(q @ np.array([P.cost(M, s["x1"] - s["xm"]) for s in tm]))
        out[name] = dict(x=x.tolist(), cash=r["h"], J=r["J"], loss_bp=r["loss_bp"], cost0_bp=bp(cost0), E_cost1_bp=bp(cost1),
                         tomorrow_binding_states=int(np.sum(np.array([s["eta"] for s in tm]) > 1e-8)),
                         E_trade_value=float(q @ np.array([np.sum(np.abs(s["x1"] - s["xm"])) for s in tm])))
        acc[f"min_cash_{name}"] = float(min(s["h"] for s in tm))
        if detail:
            out[name]["by_state"] = [dict(q=float(q[k]), trade=(s["x1"] - s["xm"]).tolist(), cash=s["h"], eta=s["eta"]) for k, s in enumerate(tm)]
    # bound terms
    t0 = time.time()
    for name in ("myopic", "plan"):
        x = R[name]["x"]; h = R[name]["h"]
        ts = time.time(); lo, hi = P.slope_box(M, nodes, x, h); t[f"slope_box_{name}"] = time.time() - ts
        ts = time.time(); b115 = P.band_115(M, x0m, x, h, lo, hi); t[f"band115_{name}"] = time.time() - ts
        ts = time.time(); cov = P.coverage(M, nodes, x, h); t[f"coverage_{name}"] = time.time() - ts
        b = dict(band115_bp=bp(b115), tail_bp=bp(cov["tail"]), eps=cov["eps"], PP=cov["PP"],
                 test_pass={str(e): bool(cov["eps"] <= e + 1e-12) for e in LEVELS},
                 VaR_Delta={str(e): var_level(cov["q"], cov["Delta"], e) for e in LEVELS}, max_need=float(cov["need"].max()), E_need=float(q @ cov["need"]),
                 min_liq=float(cov["liq"].min()))
        if name == "myopic":
            ts = time.time(); b049, Smin = P.band_049(M, lo, hi); t["band049"] = time.time() - ts
            ib, it = P.input_bound_049(M, nodes, cov)
            b.update(band049_bp=bp(b049), input_band049_bp=bp(ib), input_tail049_bp=bp(it), S_min=Smin.tolist(), S_box=[lo.tolist(), hi.tolist()])
        if detail:
            b["by_state"] = dict(need=cov["need"].tolist(), liq=cov["liq"].tolist(), D=cov["D"].tolist(), eta_bar=cov["eta_bar"].tolist(), Delta=cov["Delta"].tolist())
        out[f"bounds_{name}"] = b
    t["bounds_total"] = time.time() - t0
    # policy 2's relaxed tomorrow against per-state unbudgeted solves (accuracy)
    P2 = M.solve(x0m, h0, budget_t={0}); xr = P2["x"][0][0]; hr = P2["h"][0][0]; err = 0.0
    for k, nd in enumerate(nodes):
        mu, S = M.moments(1, nd["m"]); x1, _, _ = M.one_review(mu, S, xr * nd["g"], hr, budget=False); err = max(err, float(np.max(np.abs(x1 - P2["x"][1][k]))))
    acc["relaxed_node_err"] = err
    out["accuracy"] = acc; out["timing_s"] = t
    if detail:
        out["state_probs"] = q.tolist(); out["mu1_by_state"] = [M.moments(1, nd["m"])[0].tolist() for nd in nodes]
    return out


def purchases_diag(args):
    """Deviation 1 (diagnostic, added after the design ran): at each in-scope case's myopic and policy-2 roots, the relaxed
    tomorrow's actual purchases with their rates, sum_i (1 + kappa^+_i)(x_{1,i} - g_i x_{0,i})^+, beside claim 049's need, and
    the relaxed tomorrow's own funding shortfall (purchases + costs - cash - sales proceeds)^+. It measures how far the
    solo-target need is from what tomorrow actually buys; it changes no registered quantity."""
    regime, start, (sname, kw) = args
    M = spec.build(regime=regime, law="axis", **kw); x0m, h0 = spec.STARTS[start]; nodes = M.tree(2)[1]
    q = np.array([nd["prob"] for nd in nodes]); mu0, S0 = M.moments(0, M.m0)
    xmy, _, hmy = M.one_review(mu0, S0, x0m, h0); P2 = M.solve(x0m, h0, budget_t={0})
    rec = dict(regime=regime, start=start, setting=sname)
    for name, x, h in (("myopic", xmy, hmy), ("plan", P2["x"][0][0], P2["h"][0][0])):
        cov = P.coverage(M, nodes, x, h); buy, short = [], []
        for t in P.tomorrow(M, nodes, x, h, budget=False):
            u = t["x1"] - t["xm"]; buy.append(float(np.sum((1 + M.kp) * np.maximum(u, 0))))
            short.append(max(-t["h"], 0.0) if h >= 0 else max(-t["h"], 0.0))
        buy, short = np.array(buy), np.array(short)
        rec[name] = dict(E_need=float(q @ cov["need"]), E_relaxed_purchases=float(q @ buy), max_need=float(cov["need"].max()), max_relaxed_purchases=float(buy.max()),
                         relaxed_shortfall_states=int(np.sum(short > 1e-9)), E_relaxed_shortfall=float(q @ short), eps=cov["eps"])
    return rec


def run_diag():
    cases = list(itertools.product(REGIMES, spec.STARTS, SETTINGS))
    with mp.Pool(6) as pool:
        return pool.map(purchases_diag, cases, chunksize=1)


def design_case(args):
    regime, start, (sname, kw), negative = args
    M = spec.build(regime=regime, law="axis", negative=negative, **kw); x0m, h0 = spec.STARTS[start]
    rec = dict(regime=regime, start=start, setting=sname, negative=negative)
    rec.update(evaluate(M, x0m.copy(), h0))
    return rec


def run_design():
    cases = [(r, s, st, False) for r, s, st in itertools.product(REGIMES, spec.STARTS, SETTINGS)]
    cases += [(r, s, ("base, fund 3 short factor 2 (out of scope)", {}), True) for r, s in itertools.product(REGIMES, spec.STARTS)]
    with mp.Pool(6) as pool:
        return pool.map(design_case, cases, chunksize=1)


def run_worked():
    out = {}
    for law in ("axis", "product"):
        M = spec.build(regime="fixed-income-style", pred_alpha=0.004, law=law); x0m, h0 = spec.STARTS["rebalance"]
        t0 = time.time(); r = evaluate(M, x0m.copy(), h0, detail=True); r["wall_s"] = time.time() - t0; out[law] = r
        print("worked", law, "done", flush=True)
    return out


def run_larger():
    import scale
    out = {}
    for N, M_, K in ((30, 4, 3),):
        Mo = scale.menu(N, M_, K, "axis"); t0 = time.time()
        r = evaluate(Mo, np.zeros(Mo.n), 1.0); r["wall_s"] = time.time() - t0; r["menu"] = dict(N=N, M=M_, K=K, law="axis", seed=26)
        out[f"{N}x{M_}x{K}"] = r
    return out


ENV = dict(machine="Apple M2 Pro, 10 cores, 32 GB", os=platform.platform(), python=platform.python_version(), numpy=np.__version__,
           cvxpy=__import__("cvxpy").__version__, clarabel=__import__("clarabel").__version__)


def main():
    part = sys.argv[1] if len(sys.argv) > 1 else "all"
    dump = lambda name, obj: json.dump(dict(results=obj, env=ENV), open(HERE / f"summary_{name}.json", "w"), indent=0,
                                       default=lambda o: o.tolist() if hasattr(o, "tolist") else (bool(o) if isinstance(o, np.bool_) else float(o)))
    if part in ("design", "all"):
        dump("design", run_design()); print("design done", flush=True)
    if part in ("worked", "all"):
        dump("worked", run_worked())
    if part in ("diag", "all"):
        dump("diag", run_diag()); print("diag done", flush=True)
    if part in ("larger", "all"):
        dump("larger", run_larger()); print("larger done", flush=True)


if __name__ == "__main__":
    main()
