"""Experiment 047: claim 044 (D16's first claim; math/claim044-d16-two-review-budget at 3f485c04) against the validated
two-review harness (experiments/d16-harness). Registered design: experiments/047-claim044-two-review-budget-check.md.
Run: uv run python experiments/047/run.py
"""
import importlib.util
import json
import multiprocessing as mp
import sys
import time
from pathlib import Path

import cvxpy as cp
import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "d16-harness"))
from harness import OPT, SCALE, Model  # noqa: E402

_s = importlib.util.spec_from_file_location("run045", HERE.parent / "045" / "run.py")
m45 = importlib.util.module_from_spec(_s); _s.loader.exec_module(m45)
TOL_X = 1e-7
HSLACK = 1e-6                                          # Deviation 1: a budget with slack below 1e-6 is read as binding


def instance(i, costless=False):
    rng = np.random.default_rng([2047, 1 if costless else 0, i])
    bA = rng.uniform(0.5, 1.5); lam, al = rng.uniform(-0.01, 0.03), rng.uniform(-0.01, 0.01)
    sl, sa = rng.uniform(0.001, 0.01), rng.uniform(0.0005, 0.004)
    sA = 0.02 * np.sqrt(1 + rng.uniform(0.01, 3))
    kAp, kAm = rng.uniform(0, 0.02, 2); kEp, kEm = rng.uniform(0, 0.005, 2); cE = rng.uniform(0, 0.002)
    if costless:
        kEp = kEm = 0.0
    capA = rng.choice([0.25, 1.0])
    M = Model(bA=bA, kAp=kAp, kAm=kAm, kEp=kEp, kEm=kEm, capA=capA, cE=cE,
              theta_atoms=[(lam + a * sl, al + b * sa) for a in (1, -1) for b in (1, -1)], theta_probs=[0.25] * 4,
              z_atoms=[(a * 0.08, b * sA, 0.0) for a in (1, -1) for b in (1, -1)], z_probs=[0.25] * 4)
    x0 = np.array([rng.uniform(0, 1) * capA, 0.0 if rng.random() < 0.5 else rng.uniform(0, 0.5)])
    free = M.solve(x0, 0.0, T=2, budget=False)
    spend = [[float(np.sum(xx - xm) + M.kAp * max(xx[0] - xm[0], 0) + M.kAm * max(xm[0] - xx[0], 0) + M.kEp * max(xx[1] - xm[1], 0) + M.kEm * max(xm[1] - xx[1], 0))
              for xx, xm in [(free["x"][0][0], x0)]]]
    # the cash the budget-free program spends over both reviews: today's net purchase plus the most any state spends tomorrow
    tom = [float(np.sum(free["x"][1][k] - free["x"][0][0] * nd["g"]) + cost(M, free["x"][1][k] - free["x"][0][0] * nd["g"])) for k, nd in enumerate(free["levels"][1])]
    need = spend[0][0] + max(tom + [0.0])
    h0 = max(need * rng.uniform(0.2, 1.2), 1e-3)
    return M, x0, h0


def cost(M, u):
    return float(M.kAp * max(u[0], 0) + M.kAm * max(-u[0], 0) + M.kEp * max(u[1], 0) + M.kEm * max(-u[1], 0))


def one_review(M, mu, S, xm, hm):
    """Claim 110's one-review problem at given moments (the myopic step); holdings and the budget multiplier."""
    x = cp.Variable(2); up, dn = cp.Variable(2, nonneg=True), cp.Variable(2, nonneg=True)
    C = M.kAp * up[0] + M.kAm * dn[0] + M.kEp * up[1] + M.kEm * dn[1]
    bc = hm - cp.sum(up - dn) - C >= 0
    cons = [x - xm == up - dn, x >= 0, x[0] <= M.capA, bc]
    cp.Problem(cp.Maximize(SCALE * (mu @ x - 0.5 * M.gamma * cp.quad_form(x, cp.psd_wrap(S)) - C)), cons).solve(solver="CLARABEL", **OPT)
    return np.array(x.value), float(bc.dual_value) / SCALE, float(hm - np.sum(x.value - xm) - cost(M, x.value - xm))


def lines_lp(M, x0m, x0, h0p, nodes, x1, h1p):
    """Part 2's lines as an LP in (eta_0, eta_1[k], sigma_0[i], sigma_1[k][i], tau); returns (tau, solution)."""
    K = len(nodes); kp = np.array([M.kAp, M.kEp]); km = np.array([M.kAm, M.kEm]); cap = np.array([M.capA, np.inf])
    n = 1 + K + 2 + 2 * K + 1; iT = n - 1
    e0 = 0; e1 = lambda k: 1 + k; s0 = lambda i: 1 + K + i; s1 = lambda k, i: 1 + K + 2 + 2 * k + i
    A, b = [], []
    def le(row, rhs):
        r = row.copy(); r[iT] -= 1; A.append(r); b.append(rhs)
    def eq(row, rhs):
        le(row, rhs); le(-row, -rhs)
    def slope(idx, eidx_coef, u, i):
        """sigma in (1 + eta) T(u): eidx_coef is a row giving eta as a linear form."""
        if u > TOL_X:
            r = np.zeros(n); r[idx] = 1; r -= kp[i] * eidx_coef; eq(r, kp[i])
        elif u < -TOL_X:
            r = np.zeros(n); r[idx] = 1; r += km[i] * eidx_coef; eq(r, -km[i])
        else:
            r = np.zeros(n); r[idx] = 1; r -= kp[i] * eidx_coef; le(r, kp[i])
            r = np.zeros(n); r[idx] = -1; r -= km[i] * eidx_coef; le(r, km[i])
    def line(coefrow, const, xi, i):
        """const + coefrow . z  = 0 interior, <= 0 at zero, >= 0 at the cap."""
        at0, atc = xi <= TOL_X, xi >= cap[i] - TOL_X
        if at0 and not atc:
            le(coefrow, -const)
        elif atc and not at0:
            le(-coefrow, const)
        else:
            eq(coefrow, -const)
    beta = M.beta
    eh = np.zeros(n); eh[e0] = 1
    for k, nd in enumerate(nodes):
        eh[e1(k)] += beta * nd["prob"]
        mu, S = M.moments(1, nd["m"]); g1 = mu - M.gamma * S @ x1[k]; xm1 = x0 * nd["g"]
        ek = np.zeros(n); ek[e1(k)] = 1
        for i in range(2):
            slope(s1(k, i), ek, x1[k][i] - xm1[i], i)
            row = np.zeros(n); row[e1(k)] = -1; row[s1(k, i)] = -1
            line(row, g1[i], x1[k][i], i)
    mu0, S0 = M.moments(0, M.m0); g0 = mu0 - M.gamma * S0 @ x0
    for i in range(2):
        slope(s0(i), eh, x0[i] - x0m[i], i)
        row = -eh.copy(); row[s0(i)] -= 1
        for k, nd in enumerate(nodes):                     # + S_i = beta sum q g_i (eta_1 + sigma_1)
            row[e1(k)] += beta * nd["prob"] * nd["g"][i]; row[s1(k, i)] += beta * nd["prob"] * nd["g"][i]
        line(row, g0[i], x0[i], i)
    bounds = [(0, 0 if h0p > HSLACK else None)] + [(0, 0 if h1p[k] > HSLACK else None) for k in range(K)] + [(None, None)] * (2 + 2 * K) + [(0, None)]
    c = np.zeros(n); c[iT] = 1
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(b), bounds=bounds, method="highs")
    if res.status != 0:
        return np.inf, None
    z = res.x
    eta1 = np.array([z[e1(k)] for k in range(K)]); sig1 = np.array([[z[s1(k, i)] for i in range(2)] for k in range(K)])
    q = np.array([nd["prob"] for nd in nodes]); G = np.array([nd["g"] for nd in nodes])
    Si = beta * (q[:, None] * G * (eta1[:, None] + sig1)).sum(0); etah = z[e0] + beta * q @ eta1
    return float(res.fun), dict(eta0=float(z[e0]), eta1=eta1, S=Si, etah=float(etah), g0=g0, sig0=np.array([z[s0(0)], z[s0(1)]]))


def check(args):
    i, costless = args
    M, x0m, h0 = instance(i, costless)
    D = M.solve(x0m, h0, T=2)
    nodes = D["levels"][1]; x0 = D["x"][0][0]; x1 = D["x"][1]; h0p = D["h"][0][0]; h1p = D["h"][1]
    eta0, eta1 = D["eta"][0][0], np.array(D["eta"][1])
    tau, L = lines_lp(M, x0m, x0, h0p, nodes, x1, h1p)
    q = np.array([nd["prob"] for nd in nodes]); G = np.array([nd["g"] for nd in nodes])
    kp = np.array([M.kAp, M.kEp]); km = np.array([M.kAm, M.kEm])
    rec = dict(i=i, costless=costless, tau=tau, bind0=bool(h0p < HSLACK and eta0 > 1e-7), bind1=int(sum((h1p[k] < HSLACK) and (eta1[k] > 1e-7) for k in range(len(nodes)))),
               eta0=eta0, eta1_max=float(eta1.max()))
    # knife edges
    near = []
    for xv, xm, cp_ in [(x0[j], x0m[j], (M.capA, np.inf)[j]) for j in range(2)] + [(x1[k][j], x0[j] * nodes[k]["g"][j], (M.capA, np.inf)[j]) for k in range(len(nodes)) for j in range(2)]:
        for dd in (xv - xm, xv, cp_ - xv):
            if 1e-9 < abs(dd) < 1e-6:
                near.append(abs(dd))
    rec["edge"] = bool(near or (1e-9 < h0p < 1e-7))
    if L is not None:
        rec["eta_lp_vs_dual"] = float(max(abs(L["eta0"] - eta0), np.max(np.abs(L["eta1"] - eta1))))
        # 3(b): bounds on S_i and the buy/sell necessary conditions, with the LP's multipliers
        lo = M.beta * (q[:, None] * G * (L["eta1"][:, None] - (1 + L["eta1"][:, None]) * km)).sum(0)
        hi = M.beta * (q[:, None] * G * (L["eta1"][:, None] + (1 + L["eta1"][:, None]) * kp)).sum(0)
        rec["b3_S"] = float(max(np.max(lo - L["S"]), np.max(L["S"] - hi)))
        buy = x0 - x0m > TOL_X; sell = x0 - x0m < -TOL_X; eh = L["etah"]
        v_buy = [eh + (1 + eh) * kp[j] - hi[j] - L["g0"][j] for j in range(2) if buy[j]]
        v_sell = [L["g0"][j] - (eh - (1 + eh) * km[j] - lo[j]) for j in range(2) if sell[j]]
        rec["b3_cond"] = float(max(v_buy + v_sell + [-1.0]))
        # 4(a): claim 110's two-scalar rule at the root with (alpha~ + S, eta_hat)
        mu0, S0 = M.moments(0, M.m0); r = M.bA / M.bE; sEE = S0[1, 1]; v = S0[0, 0] - r ** 2 * sEE
        muE = mu0[1] + L["S"][1]
        o = m45.One(r=np.array([r]), mu=muE, sEE=sEE, at=np.array([mu0[0] + L["S"][0] - r * muE]), v=np.array([v]), kp=np.array([M.kAp]), km=np.array([M.kAm]),
                    cap=np.array([M.capA]), xm=np.array([x0m[0]]), kEp=M.kEp, kEm=M.kEm, pm=x0m[1], sE=0.0, h=None)
        a4 = o.at_eta(L["etah"])
        rec["a4_diff"] = float(max(abs(a4["x"][0] - x0[0]), abs(a4["p"] - x0[1])))
        # 4(d): a costless ETF (interior at the root): S_E = beta E[g_E eta_1], g_0E = eta_hat - beta E[g_E eta_1] (with the solver's duals)
        if costless and x0[1] > 1e-6:
            SE = M.beta * q @ (G[:, 1] * eta1); etah_d = eta0 + M.beta * q @ eta1
            rec["d4_line"] = float(abs(L["g0"][1] - (etah_d - SE)))
            rec["d4_S"] = float(abs(L["S"][1] - SE))
    # 3(c): the myopic policy
    mu0, S0 = M.moments(0, M.m0)
    xmy, emy0, hmy = one_review(M, mu0, S0, x0m, h0)
    x1my, e1my, h1my = [], [], []
    for nd in nodes:
        mu, S = M.moments(1, nd["m"]); xx, ee, hh = one_review(M, mu, S, xmy * nd["g"], hmy)
        x1my.append(xx); e1my.append(ee); h1my.append(hh)
    tau_my, Lmy = lines_lp(M, x0m, xmy, hmy, nodes, x1my, h1my)
    rec["my_opt_obs"] = bool(np.max(np.abs(xmy - x0)) <= 1e-5); rec["my_opt_pred"] = bool(tau_my <= 1e-6); rec["tau_my"] = tau_my
    rec["my_gap"] = float(np.max(np.abs(xmy - x0)))
    # the sign rule where it applies: myopic root buys instrument j strictly inside its box, tomorrow's regime pins s_j
    signs = []
    if not rec["my_opt_obs"]:
        e1my = np.array(e1my)
        for j in range(2):
            capj = (M.capA, np.inf)[j]
            if xmy[j] - x0m[j] > TOL_X and TOL_X < xmy[j] < capj - TOL_X and abs(x0[j] - xmy[j]) > 1e-5:
                s = []
                for k, nd in enumerate(nodes):
                    mu, S = M.moments(1, nd["m"]); g1 = (mu - M.gamma * S @ x1my[k])[j]; xm1 = xmy[j] * nd["g"][j]; u = x1my[k][j] - xm1
                    if u > TOL_X:
                        s.append(e1my[k] + (1 + e1my[k]) * kp[j])
                    elif u < -TOL_X:
                        s.append(e1my[k] - (1 + e1my[k]) * km[j])
                    elif TOL_X < x1my[k][j] < capj - TOL_X:
                        s.append(g1)
                    else:
                        s.append(None)
                if None in s:
                    signs.append(dict(j=j, pinned=False)); continue
                Sj = M.beta * q @ (G[:, j] * np.array(s)); thr = M.beta * (q @ e1my) * (1 + kp[j])
                signs.append(dict(j=j, pinned=True, crit=float(Sj - thr), dyn_minus_my=float(x0[j] - xmy[j]),
                                  ok=bool(np.sign(Sj - thr) == np.sign(x0[j] - xmy[j]))))
    rec["signs"] = signs
    return rec


def band4b(i):
    """4(b): the fund's root no-trade interval over its incumbent, by bisection, with eta_hat and S at each edge."""
    M, x0m, h0 = instance(i)
    held = lambda a: abs(M.solve(np.array([a, x0m[1]]), h0, T=2)["x"][0][0][0] - a) <= TOL_X
    grid = np.linspace(0, M.capA, 41); hs = [held(a) for a in grid]
    if not any(hs):
        return dict(i=i, empty=True)
    j0 = hs.index(True); j1 = len(hs) - 1 - hs[::-1].index(True)
    def edge(a_in, a_out):
        for _ in range(30):
            mid = 0.5 * (a_in + a_out)
            if held(mid):
                a_in = mid
            else:
                a_out = mid
        return a_in
    lo = edge(grid[j0], grid[j0 - 1]) if j0 > 0 else 0.0
    hi = edge(grid[j1], grid[j1 + 1]) if j1 < 40 else M.capA
    out = dict(i=i, empty=False, lo=lo, hi=hi, lo_at_bound=j0 == 0, hi_at_bound=j1 == 40)
    mu0, S0 = M.moments(0, M.m0); cres = M.gamma * (S0[0, 0] - S0[0, 1] ** 2 / S0[1, 1]); ceil = (M.kAp + M.kAm) / cres
    res = []
    for a, side, at_bound in ((lo, "buy", out["lo_at_bound"]), (hi, "sell", out["hi_at_bound"])):
        D = M.solve(np.array([a, x0m[1]]), h0, T=2); nodes = D["levels"][1]
        tau, L = lines_lp(M, np.array([a, x0m[1]]), D["x"][0][0], D["h"][0][0], nodes, D["x"][1], D["h"][1])
        if L is None:
            continue
        # Deviation 2: at an interior edge the fund's slope is pinned at its threshold: shift the incumbent by 1e-6 so
        # the LP pins sigma_0 = (1 + eta_hat)(kappa^+ or -kappa^-), and ask whether admissible multipliers satisfy it
        shift = -1e-6 if side == "buy" else 1e-6
        tau_edge, _ = lines_lp(M, np.array([a + shift, x0m[1]]), D["x"][0][0], D["h"][0][0], nodes, D["x"][1], D["h"][1]) if not at_bound else (None, None)
        res.append(dict(side=side, at_bound=bool(at_bound), tau_edge=tau_edge, etah=L["etah"]))
    etah_max = max(r["etah"] for r in res) if res else 0.0
    out.update(edges=res, width=hi - lo, ceiling=ceil * (1 + etah_max), within=bool(hi - lo <= ceil * (1 + etah_max) + 1e-6))
    return out


def main():
    t0 = time.time()
    with mp.Pool(8) as pool:
        main_ = pool.map(check, [(i, False) for i in range(300)], chunksize=4)
        cl = pool.map(check, [(i, True) for i in range(60)], chunksize=4)
        cands = [r["i"] for r in main_ if r["bind1"] > 0 and not r["edge"]][:10]
        b4 = pool.map(band4b, cands, chunksize=1)
    S = dict(main=main_, costless=cl, band=b4, seconds=time.time() - t0,
             statement="claim 044 at 3f485c04 (math/claim044-d16-two-review-budget; 3(b) revised at 73a6c774)")
    json.dump(S, open(HERE / "summary.json", "w"), separators=(",", ":"), default=lambda o: o.tolist() if hasattr(o, "tolist") else (bool(o) if isinstance(o, np.bool_) else float(o)))
    print("done", S["seconds"])


if __name__ == "__main__":
    main()
