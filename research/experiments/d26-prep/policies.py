"""D26 preparation (PM's note 2026-10-01-d26-start): the three policies and the bound terms of claims 049 and 115 on
harness_n's M9 tree. Preparation code, no findings; the registered experiment imports it.

Policies (one model, objective and information; LAB_REQUEST_3 section 1):
  1. myopic:  today's one-review optimum, then the funded one-review optimum at each state tomorrow;
  2. plan:    today's root of the two-review program with tomorrow's budgets dropped (today's budget kept), then the funded
              one-review optimum at each state tomorrow (no free financing in the evaluation);
  3. dynamic: the full funded two-review optimum (the benchmark).
J(x) = today's score at x net of costs + beta E[tomorrow's funded optimum from x's marked holdings and leftover cash]; review 1
is the last, so tomorrow's funded optimum is the one-review problem. Losses are V^dyn - J(x) in bp of initial wealth
W_0 = h^-_0 + sum_i x^-_{0,i} (par).

Bound terms (claims 049 and 115, at today's holding x and its cash h):
  band term   claim 049 at the myopic root: min over the admissible incumbent-value box of (1/2) S' W S, W = (gamma Sigma_0)^{-1};
              claim 115 at any x: (1/2) rho' W rho, rho the shortest g_0(x) + S - l over S in the box and l in today's line set;
  tail term   beta E[eta_bar(z') D(z')], with D = (need - liq)^+ and eps = P(D > 0) at (x, h);
  049's input-only line: (beta^2/2) sum_i (E[g_i] max(kappa^+_i, kappa^-_i))^2 norm(W) + beta eps T_eps(eta_bar D);
  115's split: PP(x) and Delta(z') = need(z') - PP(x).
They are terms of upper bounds, not a decomposition of the loss.
"""
import sys
from pathlib import Path

import cvxpy as cp
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "d16-harness"))
from harness_n import OPT  # noqa: E402

TOL = 1e-7


def cost(M, u):
    return float(M.kp @ np.maximum(u, 0) + M.km @ np.maximum(-u, 0))


def score(M, mu, S, x, xm):
    return float(mu @ x - 0.5 * M.gamma * x @ S @ x - cost(M, x - xm))


def cash_after(M, h, x, xm):
    return float(h - np.sum(x - xm) - cost(M, x - xm))


def tomorrow(M, nodes, x, h, budget=True):
    """Tomorrow's one-review optimum at every state from x's marked holdings and cash h (funded, or relaxed)."""
    out = []
    for nd in nodes:
        mu, S = M.moments(1, nd["m"]); xm = x * nd["g"]
        x1, e1, h1 = M.one_review(mu, S, xm, max(h, 0.0) if budget else h, budget=budget)
        out.append(dict(x1=x1, eta=e1, h=h1, xm=xm, mu=mu, S=S, score=score(M, mu, S, x1, xm)))
    return out


def J(M, nodes, x0m, h0, x):
    mu0, S0 = M.moments(0, M.m0); h = cash_after(M, h0, x, x0m)
    q = np.array([nd["prob"] for nd in nodes]); tm = tomorrow(M, nodes, x, h)
    return score(M, mu0, S0, x, x0m) + M.beta * float(q @ np.array([t["score"] for t in tm])), h, tm


def policies(M, x0m, h0):
    """The three roots, their values and tomorrows; V^dyn from the joint program."""
    mu0, S0 = M.moments(0, M.m0)
    D = M.solve(x0m, h0); nodes = D["levels"][1]; st_dyn = dict(M.last_stats)
    P2 = M.solve(x0m, h0, budget_t={0}); st_plan = dict(M.last_stats)
    xmy, emy, hmy = M.one_review(mu0, S0, x0m, h0)
    out = dict(V=D["value"], nodes=nodes, D=D, stats=dict(dynamic=st_dyn, plan=st_plan))
    for name, x in (("myopic", xmy), ("plan", P2["x"][0][0]), ("dynamic", D["x"][0][0])):
        v, h, tm = J(M, nodes, x0m, h0, x)
        out[name] = dict(x=x, h=h, J=v, tomorrow=tm)
    out["myopic"]["eta0"] = emy
    W0 = h0 + float(np.sum(x0m))
    for name in ("myopic", "plan", "dynamic"):
        out[name]["loss_bp"] = 1e4 * (out["V"] - out[name]["J"]) / W0
    out["W0"] = W0
    return out


def slope_box(M, nodes, x, h):
    """Claim 049/115's admissible incumbent values at the relaxed tomorrow from x: S_i in [lo_i, hi_i]."""
    q = np.array([nd["prob"] for nd in nodes]); lo = np.zeros(M.n); hi = np.zeros(M.n)
    for k, t in enumerate(tomorrow(M, nodes, x, h, budget=False)):
        g1 = t["mu"] - M.gamma * t["S"] @ t["x1"]; u = t["x1"] - t["xm"]; g = nodes[k]["g"]
        for i in range(M.n):
            if u[i] > TOL:
                a = b = M.kp[i]
            elif u[i] < -TOL:
                a = b = -M.km[i]
            elif t["x1"][i] <= TOL:
                a, b = max(g1[i], -M.km[i]), M.kp[i]
            elif np.isfinite(M.cap[i]) and t["x1"][i] >= M.cap[i] - TOL:
                a, b = -M.km[i], min(g1[i], M.kp[i])
            else:
                a = b = g1[i]
            lo[i] += M.beta * q[k] * g[i] * a; hi[i] += M.beta * q[k] * g[i] * b
    return lo, hi


def band_049(M, lo, hi):
    """min over the box of (1/2) S' W S."""
    S0 = M.moments(0, M.m0)[1]; W = np.linalg.inv(M.gamma * S0); W = (W + W.T) / 2
    S = cp.Variable(M.n); pr = cp.Problem(cp.Minimize(0.5 * cp.quad_form(S, cp.psd_wrap(W))), [S >= lo, S <= hi]); pr.solve(solver="CLARABEL", **OPT)
    return float(pr.value), np.array(S.value)


def band_115(M, x0m, x, h, lo, hi):
    """(1/2) rho' W rho: rho the shortest g_0(x) + S - l, S in [lo, hi], l = eta 1 + tau + n (tau = (1 + eta) t, t in the
    trade-sign set at x; n in the box's normal cone at x; eta = 0 if h > 0)."""
    mu0, S0 = M.moments(0, M.m0); W = np.linalg.inv(M.gamma * S0); W = (W + W.T) / 2; g0 = mu0 - M.gamma * S0 @ x; u = x - x0m
    S = cp.Variable(M.n); eta = cp.Variable(nonneg=True); tau = cp.Variable(M.n); nn = cp.Variable(M.n)
    cons = [S >= lo, S <= hi]
    if h > 1e-9:
        cons.append(eta == 0)
    for i in range(M.n):
        if u[i] > TOL:
            cons.append(tau[i] == (1 + eta) * M.kp[i])
        elif u[i] < -TOL:
            cons.append(tau[i] == -(1 + eta) * M.km[i])
        else:
            cons += [tau[i] <= (1 + eta) * M.kp[i], tau[i] >= -(1 + eta) * M.km[i]]
        if x[i] <= TOL:
            cons.append(nn[i] <= 0)
        elif np.isfinite(M.cap[i]) and x[i] >= M.cap[i] - TOL:
            cons.append(nn[i] >= 0)
        else:
            cons.append(nn[i] == 0)
    rho = g0 + S - eta * np.ones(M.n) - tau - nn
    pr = cp.Problem(cp.Minimize(0.5 * cp.quad_form(rho, cp.psd_wrap(W))), cons); pr.solve(solver="CLARABEL", **OPT)
    return float(pr.value)


def coverage(M, nodes, x, h):
    """Claim 049's per-state objects at (x, h): need, liq, D, eta_bar; and claim 115's PP and Delta."""
    q = np.array([nd["prob"] for nd in nodes]); E = np.arange(M.N, M.n)
    need, liq, eb = [], [], []
    for nd in nodes:
        mu, S = M.moments(1, nd["m"]); g = nd["g"]
        xh = np.maximum(mu - M.kp, 0) / (M.gamma * np.diag(S))
        need.append(float(np.sum((1 + M.kp) * np.maximum(xh - g * x, 0))))
        xc = (mu[E] + M.km[E]) / (M.gamma * np.diag(S)[E])
        liq.append(max(h, 0.0) + float(np.sum((1 - M.km[E]) * np.maximum(g[E] * x[E] - np.maximum(xc, 0), 0))))
        eb.append(float(np.max(np.maximum(mu - M.kp, 0) / (1 + M.kp))))
    need, liq, eb = map(np.array, (need, liq, eb)); Dsh = np.maximum(need - liq, 0)
    gmin = np.min(np.array([nd["g"] for nd in nodes]), axis=0)
    mup = M.G @ (M.Phi @ M.m0 + (np.eye(len(M.m0)) - M.Phi) @ M.theta_bar) + M.d; S1 = M.moments(1, M.m0)[1]
    xhp = np.maximum(mup - M.kp, 0) / (M.gamma * np.diag(S1)); PP = float(np.sum((1 + M.kp) * np.maximum(xhp - gmin * x, 0)))
    return dict(q=q, need=need, liq=liq, D=Dsh, eta_bar=eb, eps=float(q @ (Dsh > 0)), tail=M.beta * float(q @ (eb * Dsh)), PP=PP, Delta=need - PP)


def tail_measure(q, Y, eps):
    """Rockafellar-Uryasev T_eps(Y) = min_c c + E(Y - c)^+/eps on the finite law (the minimum is at an atom)."""
    if eps <= 0:
        return 0.0
    return float(min(c + q @ np.maximum(Y - c, 0) / eps for c in np.unique(Y)))


def input_bound_049(M, nodes, cov):
    q = np.array([nd["prob"] for nd in nodes]); Eg = q @ np.array([nd["g"] for nd in nodes])
    W = np.linalg.inv(M.gamma * M.moments(0, M.m0)[1])
    band = 0.5 * M.beta ** 2 * float(np.sum((Eg * np.maximum(M.kp, M.km)) ** 2)) * float(np.linalg.norm(W, 2))
    return band, M.beta * cov["eps"] * tail_measure(cov["q"], cov["eta_bar"] * cov["D"], cov["eps"])
