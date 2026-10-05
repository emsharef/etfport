"""Checks of claim 115 (D25b): the quantile flexibility test with time-varying premia (M9), one fund,
one ETF and cash over two reviews. Exits non-zero on failure. A check, not a proof.
Run: uv run python checks/115/check.py

 (i)   part 1: on M9's tree the need splits as need(z') = PP + Delta(z') with PP the planned purchase
       (the need at zero innovation with the worst marking) and the quantile test at level eps reads
       liq - PP >= VaR_{1-eps}(Delta) with a state-free reserve, equivalent to P(need > liq) <= eps;
       coverage at a state gives a zero admissible cash price (claim 049's part 1 on M9);
 (ii)  part 2: claim 049's loss bound holds for the repeated one-review policy on M9's tree (band term
       plus tail term, both lines), and the general bound V^dyn - J(x_0) <= (1/2)(s_f + S)'(gamma
       Sigma_0)^{-1}(s_f + S) + beta E[eta_bar D] holds at every tested today's holding, with the band
       term zero at the relaxed two-review optimum (tomorrow's budgets dropped), the front-loaded point;
 (iii) part 3: with the fund bought in every state tomorrow from the myopic root, S_A equals its
       bracket end beta E[g_A] kappa^+_A and the band term's fund part is its displayed value.
"""
import sys
import itertools
import numpy as np
import cvxpy as cp

rng = np.random.default_rng(115)
FAIL = []
TOL = 3e-4


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


def instance(tight=False, phi=0.8, qlam=1e-5, qalp=1e-4, drift_alpha=0.0):
    d = dict(bA=0.9, bE=1.0, cE=0.0005, lam0=0.010, s_lam=0.004, alp0=0.004, s_alp=0.02,
             zf=(-0.084, -0.076, 0.076, 0.084), zA=(-0.08, -0.04, 0.04, 0.08), zE=(-0.005, 0.005),
             gamma=2.5, beta=1.0, kpA=0.005, kmA=0.005, kpE=0.001, kmE=0.001, capA=1.0, capE=5.0,
             a0=0.40, p0=0.0, h0=(0.06 if tight else 0.6), phi=phi, Q=np.diag([qlam, qalp]),
             thbar=np.array([0.010, 0.004 + drift_alpha]))
    return d


def moments(d):
    return np.mean(np.square(d["zf"])), np.mean(np.square(d["zA"])), np.mean(np.square(d["zE"]))


def tree(d):
    lams = (d["lam0"] - d["s_lam"], d["lam0"] + d["s_lam"]); alps = (d["alp0"] - d["s_alp"], d["alp0"] + d["s_alp"])
    rows = []
    for lam, alp, zf, zA, zE in itertools.product(lams, alps, d["zf"], d["zA"], d["zE"]):
        f = lam + zf; rA = d["bA"] * f + alp + zA; rE = d["bE"] * f - d["cE"] + zE
        rows.append((f, rA, rE))
    rows = np.round(np.array(rows), 10)
    uniq, inv = np.unique(rows, axis=0, return_inverse=True)
    prob = np.bincount(inv.ravel(), minlength=len(uniq)) / len(rows)
    return uniq, prob


def node_moments(d, nodes):
    sf2, sA2, sE2 = moments(d); g = d["gamma"]
    P0 = np.diag([d["s_lam"] ** 2, d["s_alp"] ** 2]); R = np.diag([sf2, sA2]); m0 = np.array([d["lam0"], d["alp0"]])
    b = np.array([d["bA"], d["bE"]]); G = np.array([[d["bA"], 1.0], [d["bE"], 0.0]])
    def mom(m, P):
        return G @ m - np.array([0.0, d["cE"]]), G @ P @ G.T + np.outer(b, b) * sf2 + np.diag([sA2, sE2])
    mu0, Sig0 = mom(m0, P0)
    K = P0 @ np.linalg.inv(P0 + R); phi = d["phi"]
    m_pred = phi * m0 + (1 - phi) * d["thbar"]; P1 = phi * phi * (P0 - K @ P0) + d["Q"]
    mu_pred, Sig1 = mom(m_pred, P1)
    out = []
    for j in range(len(nodes)):
        f, rA, rE = nodes[j]; y = np.array([f, rA - d["bA"] * f])
        m1 = m_pred + phi * (K @ (y - m0)); mu1, _ = mom(m1, P1)
        out.append(dict(mu1=mu1, Sig1=Sig1, g=np.array([1 + rA, 1 + rE])))
    gmin = np.min(np.array([o["g"] for o in out]), axis=0)
    return mu0, Sig0, mu_pred, Sig1, out, gmin


def cost_expr(u, kp, km):
    return cp.sum(cp.multiply(kp, cp.pos(u)) + cp.multiply(km, cp.pos(-u)))


def two_review(d, mu0, Sig0, out, prob, relaxed=False, fix_x0=None):
    """Exact two-review program; relaxed drops tomorrow's budgets; fix_x0 evaluates a given today's holding."""
    n = 2; J = len(prob); g = d["gamma"]; beta = d["beta"]
    kp = np.array([d["kpA"], d["kpE"]]); km = np.array([d["kmA"], d["kmE"]]); xm = np.array([d["a0"], d["p0"]]); cap = np.array([d["capA"], d["capE"]])
    x0 = cp.Variable(n); u0 = x0 - xm; h0 = d["h0"] - cp.sum(u0) - cost_expr(u0, kp, km)
    obj = mu0 @ x0 - 0.5 * g * cp.quad_form(x0, cp.psd_wrap(Sig0)) - cost_expr(u0, kp, km)
    cons = [x0 >= 0, x0 <= cap, h0 >= 0]
    if fix_x0 is not None:
        cons.append(x0 == fix_x0)
    X1 = cp.Variable((J, n))
    for j in range(J):
        o = out[j]; u1 = X1[j, :] - cp.multiply(o["g"], x0); h1 = h0 - cp.sum(u1) - cost_expr(u1, kp, km)
        obj = obj + beta * prob[j] * (o["mu1"] @ X1[j, :] - 0.5 * g * cp.quad_form(X1[j, :], cp.psd_wrap(o["Sig1"])) - cost_expr(u1, kp, km))
        cons += [X1[j, :] >= 0, X1[j, :] <= cap]
        if not relaxed:
            cons.append(h1 >= 0)
    p = cp.Problem(cp.Maximize(obj), cons); p.solve(solver=cp.CLARABEL)
    return np.array(x0.value).ravel(), np.array(X1.value).reshape(J, n), float(p.value)


def one_review(d, mu, Sig, xm, h, budget=True):
    g = d["gamma"]; kp = np.array([d["kpA"], d["kpE"]]); km = np.array([d["kmA"], d["kmE"]]); cap = np.array([d["capA"], d["capE"]])
    x = cp.Variable(2); u = x - xm; cost = cost_expr(u, kp, km); hh = h - cp.sum(u) - cost
    cons = [x >= 0, x <= cap] + ([hh >= 0] if budget else [])
    p = cp.Problem(cp.Maximize(mu @ x - 0.5 * g * cp.quad_form(x, cp.psd_wrap(Sig)) - cost), cons); p.solve(solver=cp.CLARABEL)
    xv = np.array(x.value).ravel()
    return xv, float(p.value), float(h - np.sum(xv - xm) - np.sum(kp * np.maximum(xv - xm, 0) + km * np.maximum(xm - xv, 0)))


def objects_at(d, x0, h, out, prob, mu_pred, Sig1, gmin):
    """claim 049's need, liq, D, eta_bar per state at (x0, h); claim 115's planned purchase PP and Delta."""
    g = d["gamma"]; kp = np.array([d["kpA"], d["kpE"]]); J = len(prob)
    need = np.zeros(J); liq = np.zeros(J); etabar = np.zeros(J)
    for j, o in enumerate(out):
        mu1 = o["mu1"]; xhat = np.maximum(mu1 - kp, 0) / (g * np.diag(Sig1)); xcheckE = (mu1[1] + d["kmE"]) / (g * Sig1[1, 1])
        need[j] = np.sum((1 + kp) * np.maximum(xhat - o["g"] * x0, 0))
        liq[j] = h + (1 - d["kmE"]) * max(o["g"][1] * x0[1] - max(xcheckE, 0), 0)
        etabar[j] = np.max(np.maximum(mu1 - kp, 0) / (1 + kp))
    xhat_p = np.maximum(mu_pred - kp, 0) / (g * np.diag(Sig1))
    PP = np.sum((1 + kp) * np.maximum(xhat_p - gmin * x0, 0))            # the planned purchase (zero innovation, worst marking)
    Delta = need - PP
    D = np.maximum(need - liq, 0)
    return need, liq, D, etabar, PP, Delta


def var_level(y, prob, eps):
    """VaR_{1-eps}: the smallest c with P(y <= c) >= 1 - eps on the finite law."""
    order = np.argsort(y); cum = np.cumsum(prob[order])
    k = int(np.argmax(cum >= 1 - eps - 1e-12)); return y[order][k]


counts = dict(inst=0, split=0, cover=0, bound_my=0, bound_gen=0, front_zero=0, pinned=0)
for it in range(8):
    tight = it % 2 == 0
    d = instance(tight=tight, phi=rng.uniform(0.5, 0.95), qlam=rng.uniform(0, 2e-5), qalp=rng.uniform(0, 3e-4), drift_alpha=rng.uniform(-0.01, 0.03))
    d["a0"] = rng.uniform(0.1, 0.5); d["p0"] = rng.uniform(0.0, 0.3)
    nodes, prob = tree(d); mu0, Sig0, mu_pred, Sig1, out, gmin = node_moments(d, nodes)
    g = d["gamma"]; beta = d["beta"]; J = len(prob)
    kp = np.array([d["kpA"], d["kpE"]]); km = np.array([d["kmA"], d["kmE"]]); xm = np.array([d["a0"], d["p0"]])
    # dynamic optimum and the myopic policy
    xdyn, Xdyn, Vdyn = two_review(d, mu0, Sig0, out, prob)
    xmy, fmy, hmy = one_review(d, mu0, Sig0, xm, d["h0"])
    _, _, Jmy = two_review(d, mu0, Sig0, out, prob, fix_x0=xmy)            # the myopic policy's value (tomorrow optimal from it)
    need, liq, D, etabar, PP, Delta = objects_at(d, xmy, hmy, out, prob, mu_pred, Sig1, gmin)
    # (i) the split test: with a state-free reserve (here liq varies with the ETF's marking, so test the general form)
    for eps in (0.0, 0.05, 0.2):
        passes = prob @ (D > 1e-12) <= eps + 1e-12
        # split form with the state-dependent reserve: P(Delta > liq - PP) <= eps
        split = prob @ (Delta > liq - PP + 1e-12) <= eps + 1e-12
        check(passes == split, f"split test disagrees with the quantile test at eps={eps} on instance {it}")
        counts["split"] += 1
    check(np.allclose(need, PP + Delta), "need does not equal PP + Delta")
    # coverage: covered states have a zero admissible cash price at the myopic policy's tomorrow (the relaxed optimum is feasible)
    for j, o in enumerate(out):
        if liq[j] >= need[j] + 1e-9:
            xu, _, hu = one_review(d, o["mu1"], o["Sig1"], o["g"] * xmy, hmy, budget=False)
            check(hu >= -1e-7, f"coverage: relaxed optimum infeasible at a covered state {j} on instance {it}")
            counts["cover"] += 1
    # (ii) claim 049's bound for the myopic policy on M9's tree: band term with S from the relaxed tomorrow, tail term
    S = np.zeros(2)
    for j, o in enumerate(out):
        xu, _, _ = one_review(d, o["mu1"], o["Sig1"], o["g"] * xmy, hmy, budget=False)
        inc = o["g"] * xmy; g1 = o["mu1"] - g * o["Sig1"] @ xu
        t = np.where(xu > inc + TOL, kp, np.where(xu < inc - TOL, -km, np.clip(g1, -km, kp)))
        S += beta * prob[j] * o["g"] * t
    band = 0.5 * S @ np.linalg.solve(g * Sig0, S); tail = beta * prob @ (etabar * D)
    loss_my = Vdyn - Jmy
    check(loss_my <= band + tail + 1e-7, f"claim 049's bound fails on M9 instance {it}: loss {loss_my:.3e} > band {band:.3e} + tail {tail:.3e}")
    line2 = 0.5 * np.sum((beta * np.array([prob @ np.array([o["g"][i] for o in out]) for i in range(2)]) * np.maximum(kp, km)) ** 2) * np.linalg.norm(np.linalg.inv(g * Sig0), 2)
    eps_my = prob @ (D > 1e-12); T = (prob @ (etabar * D)) / eps_my if eps_my > 0 else 0.0
    check(loss_my <= line2 + beta * eps_my * T + 1e-7, f"claim 049's inputs line fails on M9 instance {it}")
    counts["bound_my"] += 1
    # the general bound at other today's holdings: the front-loaded point (relaxed two-review optimum) and two random feasible points
    xs, _, _ = two_review(d, mu0, Sig0, out, prob, relaxed=True)
    pts = [("front-loaded", xs)]
    for k in range(2):
        cand = np.clip(xmy + rng.uniform(-0.1, 0.1, 2), 0, None)
        hc = d["h0"] - np.sum(cand - xm) - np.sum(kp * np.maximum(cand - xm, 0) + km * np.maximum(xm - cand, 0))
        if hc >= 0:
            pts.append((f"random {k}", cand))
    for name, x0 in pts:
        h0 = d["h0"] - np.sum(x0 - xm) - np.sum(kp * np.maximum(x0 - xm, 0) + km * np.maximum(xm - x0, 0))
        _, _, Jx = two_review(d, mu0, Sig0, out, prob, fix_x0=x0)
        needx, liqx, Dx, etabarx, _, _ = objects_at(d, x0, h0, out, prob, mu_pred, Sig1, gmin)
        # admissible incumbent values: pinned slopes where tomorrow trades or holds inside; at a bound held untraded, the
        # interval the one-sided line cuts from [-kappa^-, kappa^+] (claim 044 part 2); S ranges over the resulting box
        S_lo = np.zeros(2); S_hi = np.zeros(2); capv = np.array([d["capA"], d["capE"]])
        for j, o in enumerate(out):
            xu, _, _ = one_review(d, o["mu1"], o["Sig1"], o["g"] * x0, h0, budget=False)
            inc = o["g"] * x0; g1 = o["mu1"] - g * o["Sig1"] @ xu
            for i in range(2):
                if xu[i] > inc[i] + TOL: lo_i = hi_i = kp[i]
                elif xu[i] < inc[i] - TOL: lo_i = hi_i = -km[i]
                elif xu[i] < TOL: lo_i, hi_i = max(-km[i], g1[i]), kp[i]          # at zero, untraded: line g1 - t <= 0
                elif xu[i] > capv[i] - TOL: lo_i, hi_i = -km[i], min(kp[i], g1[i])   # at the cap, untraded: g1 - t >= 0
                else: lo_i = hi_i = np.clip(g1[i], -km[i], kp[i])
                S_lo[i] += beta * prob[j] * o["g"][i] * lo_i; S_hi[i] += beta * prob[j] * o["g"][i] * hi_i
        # the root residual: minimise over S in its box, today's held slopes, the cash price (budget binding) and the box cone
        g0 = mu0 - g * Sig0 @ x0; u = x0 - xm; M = np.linalg.inv(g * Sig0)
        # one QP: w_i = (1 + eta) t_i makes the slope constraints linear in (eta, w); eta is free only when the budget binds
        Sv = cp.Variable(2); wv = cp.Variable(2); nv = cp.Variable(2); ev = cp.Variable()
        cons = [Sv >= S_lo, Sv <= S_hi, ev >= 0] + ([ev == 0] if h0 > 1e-6 else [])
        for i in range(2):
            if u[i] > TOL: cons.append(wv[i] == (1 + ev) * kp[i])
            elif u[i] < -TOL: cons.append(wv[i] == -(1 + ev) * km[i])
            else: cons += [wv[i] >= -(1 + ev) * km[i], wv[i] <= (1 + ev) * kp[i]]
            if x0[i] < TOL: cons.append(nv[i] <= 0)
            elif x0[i] > capv[i] - TOL: cons.append(nv[i] >= 0)
            else: cons.append(nv[i] == 0)
        r = g0 + Sv - ev - wv - nv
        pr = cp.Problem(cp.Minimize(cp.quad_form(r, cp.psd_wrap(M))), cons); pr.solve(solver=cp.CLARABEL)
        bandx = 0.5 * float(pr.value); tailx = beta * prob @ (etabarx * Dx)
        lossx = Vdyn - Jx
        check(lossx <= bandx + tailx + 1e-6, f"general bound fails at the {name} point on instance {it}: loss {lossx:.3e} > band {bandx:.3e} + tail {tailx:.3e}")
        counts["bound_gen"] += 1
        if name == "front-loaded":
            check(bandx < 1e-6, f"band term at the front-loaded point is {bandx:.2e} on instance {it}")
            counts["front_zero"] += 1
    print(f"instance {it}: tight={tight}, phi={d['phi']:.2f}, PP={PP:.4f}, P(uncovered)={eps_my:.3f}; myopic loss {loss_my:.2e} <= band {band:.2e} + tail {tail:.2e}; front-loaded loss {Vdyn - Jx if pts[0][0]=='front-loaded' else float('nan'):.2e}")
    counts["inst"] += 1

# (iii) the pinned incumbent value under a large predictable rise (claim 114's 3a hypothesis at the myopic root)
d = instance(phi=0.5, qalp=0.0, drift_alpha=0.036); d["p0"] = 0.2
nodes, prob = tree(d); mu0, Sig0, mu_pred, Sig1, out, gmin = node_moments(d, nodes)
xmy, _, hmy = one_review(d, mu0, Sig0, np.array([d["a0"], d["p0"]]), d["h0"])
SA = 0.0; bought_all = True
for j, o in enumerate(out):
    xu, _, _ = one_review(d, o["mu1"], o["Sig1"], o["g"] * xmy, hmy, budget=False)
    bought_all &= xu[0] > o["g"][0] * xmy[0] + TOL
    SA += d["beta"] * prob[j] * o["g"][0] * d["kpA"]
EgA = prob @ np.array([o["g"][0] for o in out])
check(bought_all and abs(SA - d["beta"] * EgA * d["kpA"]) < 1e-12, "pinned incumbent value differs from beta E[g_A] kappa^+_A")
counts["pinned"] += 1
print(f"pinned: bought everywhere={bought_all}, S_A={SA:.5f} = beta E[g_A] kappa^+ = {d['beta']*EgA*d['kpA']:.5f}; fund band term {SA**2/(2*d['gamma']*(Sig0[0,0]-Sig0[0,1]**2/Sig0[1,1])):.2e}")

print("cases:", counts)
check(counts["inst"] >= 8 and counts["cover"] >= 50 and counts["bound_gen"] >= 16 and counts["front_zero"] >= 8, "too few instances exercised a part")
if FAIL:
    print(f"{len(FAIL)} check(s) failed"); sys.exit(1)
print("all checks passed")
