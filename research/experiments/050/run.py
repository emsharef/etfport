"""Experiment 050: an independent check of claim 112's worked example (part 4, Tables 2-6; dacfb963) on the M8 harness.
Registered design: experiments/050-claim112-worked-example-check.md.  Run: uv run python experiments/050/run.py
checks/112 was not read.
"""
import importlib.util
import json
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "d16-harness"))
from harness import Model  # noqa: E402

_e = importlib.util.spec_from_file_location("run047", HERE.parent / "047" / "run.py"); E47 = importlib.util.module_from_spec(_e); _e.loader.exec_module(E47)
_n = importlib.util.spec_from_file_location("run049", HERE.parent / "049" / "run.py"); E49 = importlib.util.module_from_spec(_n); _n.loader.exec_module(E49)


def table1():
    return Model(bA=0.9, bE=1.0, cE=0.0005, gamma=2.5, beta=1.0, kAp=0.005, kAm=0.005, kEp=0.001, kEm=0.001, capA=1.0, capE=1.0,
                 theta_atoms=[(l, a) for l in (0.006, 0.014) for a in (-0.016, 0.024)], theta_probs=[0.25] * 4,
                 z_atoms=[(f, e, u) for f in (-0.084, -0.076, 0.076, 0.084) for e in (-0.08, -0.04, 0.04, 0.08) for u in (-0.005, 0.005)],
                 z_probs=[1 / 32] * 32, observe_factor=True)


def posterior(M, nd):
    """Finite Bayes' rule over theta's atoms at a review-1 node: mean and covariance."""
    th = np.array(M.theta_atoms); w = np.array([nd["theta_w"].get(i, 0.0) for i in range(len(th))]); w = w / w.sum()
    m = w @ th; C = (th - m).T @ np.diag(w) @ (th - m)
    return m, C


def post_moments(M, nd):
    m, C = posterior(M, nd)
    return M.G @ m + M.d, M.G @ C @ M.G.T + M.R


def main():
    M = table1(); x0m = np.array([0.40, 0.0]); h0 = 0.06; out = {}
    # Table 2
    P0, P1 = M.P(0), M.P(1); mu0, S0 = M.moments(0, M.m0)
    kl = P0[0, 0] / (P0[0, 0] + 0.08 ** 2); ka = P0[1, 1] / (P0[1, 1] + (np.std([-0.08, -0.04, 0.04, 0.08])) ** 2)
    out["t2"] = dict(P0=np.diag(P0).tolist(), gains_from_P=[1 - P1[0, 0] / P0[0, 0], 1 - P1[1, 1] / P0[1, 1]], P1=np.diag(P1).tolist(), P1_offdiag=float(P1[0, 1]),
                     mu0=mu0.tolist(), Sigma0=S0.tolist(), target0=np.linalg.solve(M.gamma * S0, mu0).tolist(),
                     shock_sd=[float(np.sqrt(M.Sz[i, i])) for i in range(3)])
    # Table 3
    lev = M.tree(2); nodes = lev[1]
    gl, ga, ew = [], [], np.zeros(2)
    for nd in nodes:
        mb, _ = posterior(M, nd); gl.append(abs(mb[0] - nd["m"][0])); ga.append(abs(mb[1] - nd["m"][1])); ew += nd["prob"] * (mb - nd["m"])
    def node(f, res, u):
        for k, nd in enumerate(nodes):
            ff, rA, rE = nd["key"]
            if abs(ff - f) < 1e-9 and abs(rA - M.bA * ff - res) < 1e-9 and abs(rE - M.bE * ff + M.cE - u) < 1e-9:
                return k
    A = node(0.090, 0.064, 0.005); B = node(0.098, 0.104, 0.005)
    out["t3"] = dict(nodes=len(nodes), max_gap_lambda=max(gl), max_gap_alpha=max(ga), expected_gap=ew.tolist(),
                     A=dict(prob=nodes[A]["prob"], filter=nodes[A]["m"].tolist(), exact=posterior(M, nodes[A])[0].tolist(),
                            prob_both_etf_shocks=nodes[A]["prob"] + nodes[node(0.090, 0.064, -0.005)]["prob"]),
                     B=dict(prob=nodes[B]["prob"], filter=nodes[B]["m"].tolist(), exact=posterior(M, nodes[B])[0].tolist(),
                            prob_both_etf_shocks=nodes[B]["prob"] + nodes[node(0.098, 0.104, -0.005)]["prob"]))
    # Table 4: myopic and dynamic at the root
    xmy, emy, hmy = E47.one_review(M, mu0, S0, x0m, h0)
    gE = (mu0 - M.gamma * S0 @ xmy)[1]; rho = S0[0, 1] / S0[1, 1]; v = S0[0, 0] - S0[0, 1] ** 2 / S0[1, 1]
    atil = mu0[0] - rho * mu0[1]; gA_red = atil + rho * gE - M.gamma * v * xmy[0]; gA = (mu0 - M.gamma * S0 @ xmy)[0]
    D = M.solve(x0m, h0, T=2)
    my_val_filter = objective(M, xmy, x0m, hmy, nodes, lambda t, nd: M.moments(0, M.m0) if t == 0 else M.moments(1, nd["m"]), policy_moments=lambda nd: M.moments(1, nd["m"]))
    out["t4"] = dict(myopic=xmy.tolist(), cash_after=hmy, eta=emy, g_E=float(gE), eta_line_E=float(emy + (1 + emy) * M.kEp), fund_marginal=float(gA),
                     fund_marginal_reduced=float(gA_red), alpha_tilde=float(atil), rho=float(rho), v=float(v), purchase_line_A=float(emy + (1 + emy) * M.kAp),
                     dynamic=D["x"][0][0].tolist(), dynamic_value=D["value"], myopic_value=my_val_filter)
    # Table 5: nodes A and B from the myopic root action
    t5 = {}
    for nm, k in (("A", A), ("B", B)):
        nd = nodes[k]; mu1, S1 = M.moments(1, nd["m"]); xm1 = xmy * nd["g"]
        x1, e1, h1 = E47.one_review(M, mu1, S1, xm1, hmy)
        mb, Sb = post_moments(M, nd); xb, eb, hb = E47.one_review(M, mb, Sb, xm1, hmy)
        # the cash price's admissible interval at this node: the one-review lines at x1 (one state, no continuation)
        rng = eta_interval(M, mu1, S1, xm1, x1, h1)
        t5[nm] = dict(marked=xm1.tolist(), cash=hmy, mu1=mu1.tolist(), target=np.linalg.solve(M.gamma * S1, mu1).tolist(), x1=x1.tolist(), eta=e1,
                      eta_interval=rng, exact_x1=xb.tolist(), exact_score_post=float(mb @ xb - 0.5 * M.gamma * xb @ Sb @ xb - E48cost(M, xb - xm1)),
                      filter_score_post=float(mb @ x1 - 0.5 * M.gamma * x1 @ Sb @ x1 - E48cost(M, x1 - xm1)),
                      # Deviation 1: Table 5's convention, the posterior mean with the filter's Sigma_1 (the claim's "with the same Sigma_1")
                      exact_x1_Sigma1=E47.one_review(M, mb, S1, xm1, hmy)[0].tolist(),
                      score_postmean_Sigma1=float(mb @ x1 - 0.5 * M.gamma * x1 @ S1 @ x1 - E48cost(M, x1 - xm1)))
    out["t5"] = t5
    # Table 6: both managers, myopic and dynamic, on the yardstick (review 0 predictive; review 1 exact posterior)
    yard = lambda t, nd: M.moments(0, M.m0) if t == 0 else post_moments(M, nd)
    res = {}
    for mgr, pm in (("filter", lambda nd: M.moments(1, nd["m"])), ("exact", lambda nd: post_moments(M, nd))):
        # myopic: review 0 at the prior (shared), review 1 at the manager's moments
        res[f"{mgr}_myopic"] = objective(M, xmy, x0m, hmy, nodes, yard, policy_moments=pm)
        # dynamic: the manager's own two-review program, then scored on the yardstick
        Dm = M.solve(x0m, h0, T=2, moments_fn=(lambda t, nd, pm=pm: M.moments(0, M.m0) if t == 0 else pm(nd)))
        x0d = Dm["x"][0][0]; val = score(M, *M.moments(0, M.m0), x0d, x0m)
        for k, nd in enumerate(nodes):
            mu, S = yard(1, nd); val += M.beta * nd["prob"] * score(M, mu, S, Dm["x"][1][k], x0d * nd["g"])
        res[f"{mgr}_dynamic"] = val; res[f"{mgr}_dynamic_root"] = x0d.tolist(); res[f"{mgr}_dynamic_own_value"] = Dm["value"]
        res[f"{mgr}_x1"] = [x.tolist() for x in Dm["x"][1]]
    differ = sum(np.max(np.abs(np.array(a) - np.array(b))) > 1e-6 for a, b in zip(res["filter_x1"], res["exact_x1"]))
    myd = 0
    for nd in nodes:
        xm1 = xmy * nd["g"]
        a1 = E47.one_review(M, *M.moments(1, nd["m"]), xm1, hmy)[0]; b1 = E47.one_review(M, *post_moments(M, nd), xm1, hmy)[0]
        myd += np.max(np.abs(a1 - b1)) > 1e-6
    out["t6"] = dict(**{k: v for k, v in res.items() if not k.endswith("_x1")}, gain_myopic_bp=1e4 * (res["exact_myopic"] - res["filter_myopic"]),
                     gain_dynamic_bp=1e4 * (res["exact_dynamic"] - res["filter_dynamic"]), nodes_differ_dynamic=int(differ), nodes_differ_myopic=int(myd))
    json.dump(out, open(HERE / "summary.json", "w"), indent=1, default=lambda o: o.tolist() if hasattr(o, "tolist") else float(o))
    print(json.dumps(out, indent=1, default=float))


def E48cost(M, u):
    return float(M.kAp * max(u[0], 0) + M.kAm * max(-u[0], 0) + M.kEp * max(u[1], 0) + M.kEm * max(-u[1], 0))


def score(M, mu, S, x, xm):
    return float(mu @ x - 0.5 * M.gamma * x @ S @ x - E48cost(M, x - xm))


def objective(M, x0, x0m, h0p, nodes, yard, policy_moments):
    """The myopic policy from root action x0: review 1 by the one-review rule at policy_moments; scored on yard."""
    val = score(M, *yard(0, None), x0, x0m)
    for nd in nodes:
        xm1 = x0 * nd["g"]; x1 = E47.one_review(M, *policy_moments(nd), xm1, h0p)[0]
        val += M.beta * nd["prob"] * score(M, *yard(1, nd), x1, xm1)
    return val


def eta_interval(M, mu, S, xm, x, h):
    """The admissible cash-price interval of a one-review problem at its solution x (claim 110's lines, LP)."""
    from scipy.optimize import linprog
    kp = np.array([M.kAp, M.kEp]); km = np.array([M.kAm, M.kEm]); g = mu - M.gamma * S @ x
    # variables (eta, s_A, s_E); lines: g_i - eta - s_i = 0 interior (<= 0 at zero), s_i in (1 + eta) T_i
    A, b = [], []
    for i in range(2):
        u = x[i] - xm[i]; r = np.zeros(3); r[0] = 1; r[1 + i] = 1
        if x[i] <= 1e-9:
            A.append(-r); b.append(-g[i])
        else:
            A.append(r); b.append(g[i]); A.append(-r); b.append(-g[i])
        rr = np.zeros(3); rr[1 + i] = 1
        if u > 1e-9:
            e = rr.copy(); e[0] = -kp[i]; A.append(e); b.append(kp[i]); A.append(-e); b.append(-kp[i])
        elif u < -1e-9:
            e = rr.copy(); e[0] = km[i]; A.append(e); b.append(-km[i]); A.append(-e); b.append(km[i])
        else:
            e = rr.copy(); e[0] = -kp[i]; A.append(e); b.append(kp[i]); e2 = -rr.copy(); e2[0] = -km[i]; A.append(e2); b.append(km[i])
    bounds = [(0, 0 if h > 1e-6 else None), (None, None), (None, None)]
    lo = linprog([1, 0, 0], A_ub=np.array(A), b_ub=np.array(b) + 1e-10, bounds=bounds, method="highs")
    hi = linprog([-1, 0, 0], A_ub=np.array(A), b_ub=np.array(b) + 1e-10, bounds=bounds, method="highs")
    return [float(lo.x[0]) if lo.status == 0 else None, float(hi.x[0]) if hi.status == 0 else None]


if __name__ == "__main__":
    main()
