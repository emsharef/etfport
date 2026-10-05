"""Solver checks of claim 113 (D20): several funds sharing one ETF and cash over two reviews in M8's
setting (M7's finite-law variant with N funds, one ETF, one factor, T = 2, the funded budget).

The two-review problem is solved exactly as one concave program over the public tree with
cvxpy/CLARABEL (floating point, not a certificate); the node budgets' duals give tomorrow's cash
prices. Exits non-zero on failure. A check, not a proof. Run: uv run python checks/113/check.py

 (i)   part 1: at the dynamic root every fund's holding is claim 110's clip at the root's exposure
       price and dynamic cash price with its incumbent value added to its net alpha (the root lines
       of claim 044 with N funds), and the ETF's root line holds;
 (ii)  part 2: at every state where today's cash plus the ETF's sale proceeds down to its solo sale
       threshold cover the funds' aggregate solo-target purchases, tomorrow's cash price is zero;
       and tomorrow's cash price never exceeds the best expected return net of its purchase rate,
       scaled, at states that buy;
 (iii) part 3: a fund's dynamic-minus-myopic root move has the sign of its own residual corrected by
       the two shared scalars' changes (the exposure price and the cash price), when the fund trades
       strictly inside its box at both roots; and the pooling identity for the maximal need;
 (iv)  the reserve identity: ETF plus cash reserve equals the funds' holdings foregone plus the
       cost difference.
"""
import sys
import itertools
import numpy as np
import cvxpy as cp

rng = np.random.default_rng(113)
FAIL = []
TOL = 3e-4
MTOL = 5e-5


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


def instance(N, tight, shock_pts=4):
    """N funds, one ETF, one factor; finite laws as in claim 112's example, the fund residuals independent."""
    d = dict(N=N, bE=1.0, cE=0.0005, lam0=0.010, s_lam=0.004, gamma=2.5, beta=1.0,
             zf=(-0.084, -0.076, 0.076, 0.084), zE=(-0.005, 0.005), kpE=0.001, kmE=0.001, capE=5.0)
    d["bA"] = rng.uniform(0.7, 1.1, N)
    d["alp0"] = rng.uniform(0.002, 0.008, N)
    d["s_alp"] = np.full(N, 0.02)
    d["zA"] = (-0.08, -0.04, 0.04, 0.08) if shock_pts == 4 else (-0.0632, 0.0632)
    d["kpA"] = rng.uniform(0.003, 0.010, N); d["kmA"] = rng.uniform(0.003, 0.010, N)
    d["capA"] = np.full(N, 1.0)
    d["a0"] = rng.uniform(0.05, 0.35, N); d["p0"] = rng.uniform(0.0, 0.2) * (rng.uniform() < 0.6)
    d["h0"] = rng.uniform(0.0, 0.05) if tight else rng.uniform(0.3, 0.6)
    return d


def moments(d):
    return np.mean(np.square(d["zf"])), np.mean(np.square(d["zA"])), np.mean(np.square(d["zE"]))


def tree(d):
    """Public nodes at review 1: (f, s_1..s_N, e) with s_i the fund residual observation and e the ETF residual; probabilities."""
    N = d["N"]; lams = (d["lam0"] - d["s_lam"], d["lam0"] + d["s_lam"])
    hidden = []
    for lam in lams:
        for zf in d["zf"]:
            f = lam + zf
            for alps in itertools.product(*[(d["alp0"][i] - d["s_alp"][i], d["alp0"][i] + d["s_alp"][i]) for i in range(N)]):
                for zAs in itertools.product(d["zA"], repeat=N):
                    for zE in d["zE"]:
                        s = tuple(alps[i] + zAs[i] for i in range(N))
                        hidden.append((f,) + s + (zE,))
    hidden = np.round(np.array(hidden), 10)
    uniq, inv = np.unique(hidden, axis=0, return_inverse=True)
    prob = np.bincount(inv.ravel(), minlength=len(uniq)) / len(hidden)
    return uniq, prob


def beliefs_and_moments(d, nodes):
    """Filter means at each node and the (common) review-1 covariance; review-0 moments."""
    N = d["N"]; sf2, sA2, sE2 = moments(d); g = d["gamma"]
    plam0, palp0 = d["s_lam"] ** 2, d["s_alp"] ** 2
    klam = plam0 / (plam0 + sf2); kalp = palp0 / (palp0 + sA2)
    plam1 = (1 - klam) * plam0; palp1 = (1 - kalp) * palp0
    def mom(lam, alp, plam, palp):
        b = np.concatenate([d["bA"], [d["bE"]]])
        mu = np.concatenate([d["bA"] * lam + alp, [d["bE"] * lam - d["cE"]]])
        Sig = np.outer(b, b) * (sf2 + plam) + np.diag(np.concatenate([sA2 + palp, [sE2]]))
        return mu, Sig
    mu0, Sig0 = mom(d["lam0"], d["alp0"], plam0, palp0)
    f = nodes[:, 0]; S = nodes[:, 1:1 + N]
    lam1 = d["lam0"] + klam * (f - d["lam0"])
    alp1 = d["alp0"][None, :] + kalp[None, :] * (S - d["alp0"][None, :])
    mus1 = [mom(lam1[j], alp1[j], plam1, palp1)[0] for j in range(len(nodes))]
    Sig1 = mom(lam1[0], alp1[0], plam1, palp1)[1]
    gross = np.column_stack([1 + d["bA"][None, :] * f[:, None] + S, 1 + d["bE"] * f - d["cE"] + nodes[:, 1 + N]])   # gross returns per node
    return mu0, Sig0, mus1, Sig1, gross


def cost_expr(u, kp, km):
    return cp.sum(cp.multiply(kp, cp.pos(u)) + cp.multiply(km, cp.pos(-u)))


def solve_two_review(d, mu0, Sig0, mus1, Sig1, gross, prob):
    N = d["N"]; n = N + 1; J = len(prob); g = d["gamma"]; beta = d["beta"]
    kp = np.concatenate([d["kpA"], [d["kpE"]]]); km = np.concatenate([d["kmA"], [d["kmE"]]])
    xm = np.concatenate([d["a0"], [d["p0"]]]); cap = np.concatenate([d["capA"], [d["capE"]]])
    x0 = cp.Variable(n); u0 = x0 - xm
    h0 = d["h0"] - cp.sum(u0) - cost_expr(u0, kp, km)
    obj = mu0 @ x0 - 0.5 * g * cp.quad_form(x0, cp.psd_wrap(Sig0)) - cost_expr(u0, kp, km)
    cons = [x0 >= 0, x0 <= cap]; c_h0 = h0 >= 0; cons.append(c_h0)
    X1 = cp.Variable((J, n)); node_cons = []
    for j in range(J):
        u1 = X1[j, :] - cp.multiply(gross[j], x0)
        h1 = h0 - cp.sum(u1) - cost_expr(u1, kp, km)
        obj = obj + beta * prob[j] * (mus1[j] @ X1[j, :] - 0.5 * g * cp.quad_form(X1[j, :], cp.psd_wrap(Sig1)) - cost_expr(u1, kp, km))
        c = h1 >= 0; node_cons.append(c); cons += [c, X1[j, :] >= 0, X1[j, :] <= cap]
    p = cp.Problem(cp.Maximize(obj), cons); p.solve(solver=cp.CLARABEL)
    x0v = np.array(x0.value).ravel(); X1v = np.array(X1.value)
    eta0 = float(c_h0.dual_value); eta1 = np.array([float(c.dual_value) / (beta * prob[j]) for j, c in enumerate(node_cons)])
    h0v = d["h0"] - np.sum(x0v - xm) - np.sum(kp * np.maximum(x0v - xm, 0) + km * np.maximum(xm - x0v, 0))
    return x0v, X1v, eta0, eta1, h0v, float(p.value)


def solve_one_review(d, mu, Sig, xm, h):
    N = d["N"]; n = N + 1; g = d["gamma"]
    kp = np.concatenate([d["kpA"], [d["kpE"]]]); km = np.concatenate([d["kmA"], [d["kmE"]]])
    cap = np.concatenate([d["capA"], [d["capE"]]])
    x = cp.Variable(n); u = x - xm
    hh = h - cp.sum(u) - cost_expr(u, kp, km)
    p = cp.Problem(cp.Maximize(mu @ x - 0.5 * g * cp.quad_form(x, cp.psd_wrap(Sig)) - cost_expr(u, kp, km)), [x >= 0, x <= cap, hh >= 0])
    p.solve(solver=cp.CLARABEL)
    xv = np.array(x.value).ravel()
    return xv, float(p.constraints[2].dual_value), float(h - np.sum(xv - xm) - np.sum(kp * np.maximum(xv - xm, 0) + km * np.maximum(xm - xv, 0)))


counts = dict(inst=0, root_funds=0, noreserve_states=0, capbound_states=0, sign=0, pool_strict=0, tight=0)
for it in range(18):
    N = 2 if it % 3 != 2 else 3
    d = instance(N, tight=(it % 2 == 0), shock_pts=4 if N == 2 else 2)
    nodes, prob = tree(d)
    mu0, Sig0, mus1, Sig1, gross = beliefs_and_moments(d, nodes)
    x0, X1, eta0, eta1, h0, val = solve_two_review(d, mu0, Sig0, mus1, Sig1, gross, prob)
    J = len(prob); g = d["gamma"]; beta = d["beta"]
    kp = np.concatenate([d["kpA"], [d["kpE"]]]); km = np.concatenate([d["kmA"], [d["kmE"]]])
    xm = np.concatenate([d["a0"], [d["p0"]]])
    # tomorrow's slopes and incumbent values s_i(z') from the solved states
    S = np.zeros(N + 1)
    for j in range(J):
        inc = gross[j] * x0; x1 = X1[j]; g1 = mus1[j] - g * Sig1 @ x1
        for i in range(N + 1):
            if x1[i] > inc[i] + TOL:
                t = kp[i]
            elif x1[i] < inc[i] - TOL:
                t = -km[i]
            else:
                t = np.clip((g1[i] - eta1[j]) / (1 + eta1[j]), -km[i], kp[i])
            S[i] += beta * prob[j] * gross[j, i] * (eta1[j] + (1 + eta1[j]) * t)
    eta_hat = eta0 + beta * prob @ eta1
    # (i) root lines through claim 110's clip: exposure price m_0 = mu_E - gamma sigma_EE w_0 (sigma_EE the factor part)
    sf2, sA2, sE2 = moments(d); plam0 = d["s_lam"] ** 2
    sEE = d["bE"] ** 2 * (sf2 + plam0); r = d["bA"] / d["bE"]; v = np.diag(Sig0)[:N] - r * r * sEE
    at = mu0[:N] - r * mu0[N]
    w0 = x0[N] + r @ x0[:N]; m0 = mu0[N] - g * sEE * w0
    lo = (at + S[:N] + r * m0 - eta_hat - (1 + eta_hat) * d["kpA"]) / (g * v)
    hi = (at + S[:N] + r * m0 - eta_hat + (1 + eta_hat) * d["kmA"]) / (g * v)
    clip = np.clip(np.clip(d["a0"], lo, hi), 0.0, d["capA"])
    check(np.max(np.abs(clip - x0[:N])) < 5 * TOL, f"part 1: root fund holdings differ from the clip at (m_0, eta_hat) with alpha~ + S on instance {it}: {np.max(np.abs(clip - x0[:N])):.2e}")
    counts["root_funds"] += N
    # the ETF's root line: m_0 - gamma sigma_E p_0 + S_E = eta_hat + (1 + eta_hat) t_E - zeta
    gE0 = m0 - g * sE2 * x0[N] + S[N]
    if x0[N] > d["p0"] + TOL:
        check(abs(gE0 - (eta_hat + (1 + eta_hat) * d["kpE"])) < MTOL, f"part 1: ETF root line (bought) fails on instance {it}")
    elif TOL < x0[N] < d["p0"] - TOL:
        check(abs(gE0 - (eta_hat - (1 + eta_hat) * d["kmE"])) < MTOL, f"part 1: ETF root line (sold) fails on instance {it}")
    elif x0[N] < TOL:
        check(gE0 <= eta_hat + (1 + eta_hat) * (d["kpE"] if d["p0"] < TOL else -d["kmE"]) + MTOL, f"part 1: ETF root line (at zero) fails on instance {it}")
    else:
        check(eta_hat - (1 + eta_hat) * d["kmE"] - MTOL <= gE0 <= eta_hat + (1 + eta_hat) * d["kpE"] + MTOL, f"part 1: ETF root line (idle) fails on instance {it}")
    # (ii) no-reserve test with the ETF as reserve, and the cash-price bound
    for j in range(J):
        mu1 = mus1[j]
        xhat = np.maximum(mu1[:N] - d["kpA"], 0) / (g * np.diag(Sig1)[:N])
        xhatE_sale = (mu1[N] + d["kmE"]) / (g * Sig1[N, N])          # the ETF's solo sale threshold
        xhatE = max(mu1[N] - d["kpE"], 0) / (g * Sig1[N, N])            # the ETF's solo purchase target
        need = np.sum((1 + d["kpA"]) * np.maximum(xhat - gross[j, :N] * x0[:N], 0)) + (1 + d["kpE"]) * max(xhatE - gross[j, N] * x0[N], 0.0)
        liq = h0 + (1 - d["kmE"]) * max(gross[j, N] * x0[N] - max(xhatE_sale, 0.0), 0.0)   # threshold clipped at zero (leanb)
        if liq >= need + 1e-9:
            # eta_1 = 0 is admissible: the node's lines hold with eta = 0 for some slopes (the solver's dual may sit
            # elsewhere in the multiplier interval when the state trades nothing with all cash spent, claim 046's 1c)
            inc = gross[j] * x0; x1 = X1[j]; g1 = mu1 - g * Sig1 @ x1; ok = True
            for i in range(N + 1):
                if x1[i] > inc[i] + TOL:
                    ok &= abs(g1[i] - kp[i]) < MTOL if x1[i] < (np.concatenate([d["capA"], [d["capE"]]])[i] - TOL) else g1[i] >= kp[i] - MTOL
                elif x1[i] < inc[i] - TOL:
                    ok &= abs(g1[i] + km[i]) < MTOL if x1[i] > TOL else g1[i] <= -km[i] + MTOL
                else:
                    ok &= (g1[i] <= kp[i] + MTOL) and (x1[i] < TOL or g1[i] >= -km[i] - MTOL)
            check(ok, f"part 2: liquidity {liq:.4f} covers the need {need:.4f} but eta_1 = 0 is not admissible at node {j} on instance {it}: inc {np.round(inc,4)} x1 {np.round(x1,4)} g1 {np.round(g1,5)} kp {np.round(kp,4)} km {np.round(km,4)} eta1 {eta1[j]:.2e} xhat {np.round(xhat,4)} xhatE {xhatE:.4f}")
            counts["noreserve_states"] += 1
        bought = np.any(X1[j] > gross[j] * x0 + TOL)
        if bought:
            etabar = np.max(np.maximum(mu1 - kp, 0) / (1 + kp))
            check(eta1[j] <= etabar + 1e-6, f"part 2: eta_1 {eta1[j]:.4f} above eta_bar {etabar:.4f} at a buying node {j} on instance {it}")
            counts["capbound_states"] += 1
    # (iii) the sign statement against the myopic root, and pooling
    xmy, etamy, hmy = solve_one_review(d, mu0, Sig0, xm, d["h0"])
    wmy = xmy[N] + r @ xmy[:N]; mmy = mu0[N] - g * sEE * wmy
    for i in range(N):
        dyn_int = d["a0"][i] + TOL < x0[i] < d["capA"][i] - TOL or TOL < x0[i] < d["a0"][i] - TOL
        my_int = d["a0"][i] + TOL < xmy[i] < d["capA"][i] - TOL or TOL < xmy[i] < d["a0"][i] - TOL
        same_dir = np.sign(x0[i] - d["a0"][i]) == np.sign(xmy[i] - d["a0"][i])
        if dyn_int and my_int and same_dir:
            kap = d["kpA"][i] if x0[i] > d["a0"][i] else -d["kmA"][i]
            bracket = S[i] + r[i] * (m0 - mmy) - (eta_hat - etamy) * (1 + kap)
            if abs(bracket) > 1e-6 and abs(x0[i] - xmy[i]) > TOL:
                check(np.sign(bracket) == np.sign(x0[i] - xmy[i]), f"part 3: sign of fund {i}'s move differs from its corrected residual on instance {it}")
                counts["sign"] += 1
    needs = np.zeros((J, N))
    for j in range(J):
        xhat = np.maximum(mus1[j][:N] - d["kpA"], 0) / (g * np.diag(Sig1)[:N])
        needs[j] = (1 + d["kpA"]) * np.maximum(xhat - gross[j, :N] * x0[:N], 0)
    max_agg = np.max(needs.sum(1)); sum_max = np.sum(needs.max(0))
    check(max_agg <= sum_max + 1e-12, "pooling inequality fails")
    counts["pool_strict"] += int(max_agg < sum_max - 1e-9)
    # (iv) the reserve identity
    def cost(x):
        return np.sum(kp * np.maximum(x - xm, 0) + km * np.maximum(xm - x, 0))
    R = (x0[N] + h0) - (xmy[N] + hmy)
    check(abs(R - ((np.sum(xmy[:N]) - np.sum(x0[:N])) + (cost(xmy) - cost(x0)))) < 1e-8, f"reserve identity fails on instance {it}")
    counts["inst"] += 1; counts["tight"] += int(eta0 > 1e-5 or np.max(eta1) > 1e-5)
    print(f"instance {it}: N={N}, nodes={J}, eta_0={eta0:.4f}, E eta_1={prob @ eta1:.4f}, reserve (ETF+cash, dynamic - myopic) {R:+.4f}; max aggregate need {max_agg:.4f} vs sum of maxima {sum_max:.4f}")

print("cases:", counts)
check(counts["inst"] >= 15 and counts["noreserve_states"] >= 50 and counts["capbound_states"] >= 50 and counts["sign"] >= 4 and counts["tight"] >= 6, "too few instances exercised a part")
if FAIL:
    print(f"{len(FAIL)} check(s) failed"); sys.exit(1)
print("all checks passed")
