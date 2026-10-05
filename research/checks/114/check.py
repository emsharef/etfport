"""Checks of claim 114 (D24): time-varying premia and alphas (M9: M8 with M5's state equation,
Phi != I, Q != 0) over two reviews, one fund, one ETF and cash.

Exits non-zero on failure. A check, not a proof. Run: uv run python checks/114/check.py

 (i)   part 1: the target's move splits into the predictable part (known at review 0, in Phi, Q,
       theta_bar, the beliefs and the risk-charge change) and the innovation part, whose
       unconditional mean is zero and whose covariance is the filter's innovation covariance
       propagated by Phi, on the finite tree;
 (ii)  part 2: the root band of a lone fund (no ETF, no budget) in the coarse regime is claim 029's
       static band shifted by the tilt beta (kappa^+ U - kappa^- D)/c with U and D the probabilities
       that the target rises and falls, which under a symmetric innovation law and equal rates is
       beta kappa P(|innovation| <= |predictable move|)/c toward the predictable move;
 (iii) part 3: with the fund bought tomorrow in every state (a large predictable rise), its incumbent
       value sits at its upper bracket and the dynamic root holds at least the myopic root's fund
       (front-loading) when today's budget is slack; and with the fund sold tomorrow in every state
       the mirror; the need tomorrow equals its predictable part plus the innovation part;
 (iv)  part 4: the two-review criterion (claims 044/046/047/113) transfers: the root clip with
       alpha~ + S at (m_0, eta_hat_0), and the aggregate no-reserve test, hold on M9's tree.
"""
import sys
import itertools
import numpy as np
import cvxpy as cp

rng = np.random.default_rng(114)
FAIL = []
TOL = 3e-4
MTOL = 5e-5


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


# ------------------------------------------------------------------ M9 filter with Phi, Q (one factor, one fund)
def filter_step(m0, P0, phi, Q, thbar, R, y_minus_d):
    """One M5 update with persistence: theta_{t+1} = Phi theta_t + (I - Phi) theta_bar + eta. Observation y = H theta_t + d + noise,
    H = I (the transformed observation observes theta_t directly), R diagonal. Returns m_1, P_1, K_0, the predictable mean and the innovation."""
    K = P0 @ np.linalg.inv(P0 + R)                     # H = I
    nu = y_minus_d - m0                                 # innovation
    m_pred = phi * m0 + (1 - phi) * thbar               # predictable part of m_1 (Phi = phi I)
    m1 = m_pred + phi * (K @ nu)
    P1 = phi * phi * (P0 - K @ P0) + Q
    return m1, P1, K, m_pred, phi * (K @ nu)


def instance(tight=False, phi=0.8, qlam=1e-5, qalp=1e-4, drift_alpha=0.0):
    d = dict(bA=0.9, bE=1.0, cE=0.0005, lam0=0.010, s_lam=0.004, alp0=0.004, s_alp=0.02,
             zf=(-0.084, -0.076, 0.076, 0.084), zA=(-0.08, -0.04, 0.04, 0.08), zE=(-0.005, 0.005),
             gamma=2.5, beta=1.0, kpA=0.005, kmA=0.005, kpE=0.001, kmE=0.001, capA=1.0, capE=5.0,
             a0=0.40, p0=0.0, h0=(0.06 if tight else 0.6), phi=phi, Q=np.diag([qlam, qalp]),
             thbar=np.array([0.010, 0.004 + drift_alpha]),      # long-run means; drift_alpha shifts alpha's long-run mean
             eta_lam=(-np.sqrt(qlam), np.sqrt(qlam)), eta_alp=(-np.sqrt(qalp), np.sqrt(qalp)))
    return d


def moments(d):
    return np.mean(np.square(d["zf"])), np.mean(np.square(d["zA"])), np.mean(np.square(d["zE"]))


def tree(d):
    """Hidden branches (theta_0, z_1) at review 1; public y_1 = (f, r^A, r^E). (The state shock eta_1 affects returns
    after review 1 only, so the two-review objective does not see it beyond m_1, P_1.)"""
    lams = (d["lam0"] - d["s_lam"], d["lam0"] + d["s_lam"]); alps = (d["alp0"] - d["s_alp"], d["alp0"] + d["s_alp"])
    rows = []
    for lam, alp, zf, zA, zE in itertools.product(lams, alps, d["zf"], d["zA"], d["zE"]):
        f = lam + zf; rA = d["bA"] * f + alp + zA; rE = d["bE"] * f - d["cE"] + zE
        rows.append((lam, alp, f, rA, rE))
    rows = np.round(np.array(rows), 10)
    uniq, inv = np.unique(rows[:, 2:], axis=0, return_inverse=True)
    prob = np.bincount(inv.ravel(), minlength=len(uniq)) / len(rows)
    return uniq, prob


def node_moments(d, nodes):
    sf2, sA2, sE2 = moments(d); g = d["gamma"]
    P0 = np.diag([d["s_lam"] ** 2, d["s_alp"] ** 2]); R = np.diag([sf2, sA2]); m0 = np.array([d["lam0"], d["alp0"]])
    b = np.array([d["bA"], d["bE"]])
    G = np.array([[d["bA"], 1.0], [d["bE"], 0.0]])
    def mom(m, P):
        mu = G @ m - np.array([0.0, d["cE"]])
        Sig = G @ P @ G.T + np.outer(b, b) * sf2 + np.diag([sA2, sE2])        # G P G' + Sigma_r
        return mu, Sig
    mu0, Sig0 = mom(m0, P0)
    out = []
    for j in range(len(nodes)):
        f, rA, rE = nodes[j]
        y = np.array([f, rA - d["bA"] * f])                # observes theta_0 with noise (z^f, z^A)
        m1, P1, K, m_pred, innov = filter_step(m0, P0, d["phi"], d["Q"], d["thbar"], R, y)
        mu1, Sig1 = mom(m1, P1)
        out.append(dict(m1=m1, P1=P1, mu1=mu1, Sig1=Sig1, m_pred=m_pred, innov=innov, K=K, g=np.array([1 + rA, 1 + rE])))
    return mu0, Sig0, m0, P0, out


def two_review(d, mu0, Sig0, nodes_out, prob, fund_only=False, no_budget=False):
    n = 1 if fund_only else 2; J = len(prob); g = d["gamma"]; beta = d["beta"]
    kp = np.array([d["kpA"], d["kpE"]])[:n]; km = np.array([d["kmA"], d["kmE"]])[:n]
    xm = np.array([d["a0"], d["p0"]])[:n]; cap = np.array([d["capA"], d["capE"]])[:n]
    def cost(u):
        return cp.sum(cp.multiply(kp, cp.pos(u)) + cp.multiply(km, cp.pos(-u)))
    x0 = cp.Variable(n); u0 = x0 - xm
    h0 = d["h0"] - cp.sum(u0) - cost(u0)
    obj = mu0[:n] @ x0 - 0.5 * g * cp.quad_form(x0, cp.psd_wrap(Sig0[:n, :n])) - cost(u0)
    cons = [x0 >= 0, x0 <= cap]
    c_h0 = h0 >= 0
    if not no_budget:
        cons.append(c_h0)
    X1 = cp.Variable((J, n)); node_cons = []
    for j in range(J):
        o = nodes_out[j]
        u1 = X1[j, :] - cp.multiply(o["g"][:n], x0)
        h1 = h0 - cp.sum(u1) - cost(u1)
        obj = obj + beta * prob[j] * (o["mu1"][:n] @ X1[j, :] - 0.5 * g * cp.quad_form(X1[j, :], cp.psd_wrap(o["Sig1"][:n, :n])) - cost(u1))
        cons += [X1[j, :] >= 0, X1[j, :] <= cap]
        if not no_budget:
            c = h1 >= 0; node_cons.append(c); cons.append(c)
    p = cp.Problem(cp.Maximize(obj), cons); p.solve(solver=cp.CLARABEL)
    x0v = np.array(x0.value).ravel(); X1v = np.array(X1.value).reshape(J, n)
    eta0 = 0.0 if no_budget else float(c_h0.dual_value)
    eta1 = np.zeros(J) if no_budget else np.array([float(c.dual_value) / (beta * prob[j]) for j, c in enumerate(node_cons)])
    return x0v, X1v, eta0, eta1, float(p.value)


def one_review(d, mu, Sig, xm, h, n=2):
    g = d["gamma"]; kp = np.array([d["kpA"], d["kpE"]])[:n]; km = np.array([d["kmA"], d["kmE"]])[:n]; cap = np.array([d["capA"], d["capE"]])[:n]
    x = cp.Variable(n); u = x - xm
    cost = cp.sum(cp.multiply(kp, cp.pos(u)) + cp.multiply(km, cp.pos(-u)))
    hh = h - cp.sum(u) - cost
    p = cp.Problem(cp.Maximize(mu[:n] @ x - 0.5 * g * cp.quad_form(x, cp.psd_wrap(Sig[:n, :n])) - cost), [x >= 0, x <= cap, hh >= 0])
    p.solve(solver=cp.CLARABEL)
    return np.array(x.value).ravel(), float(p.constraints[2].dual_value)


counts = dict(decomp=0, tilt=0, front=0, back=0, transfer=0, noreserve=0)

# (i) the decomposition of the target's move on the tree, for several (phi, Q)
for phi, qa in ((1.0, 0.0), (0.8, 1e-4), (0.6, 4e-4), (0.9, 0.0)):
    d = instance(phi=phi, qalp=qa)
    nodes, prob = tree(d); mu0, Sig0, m0, P0, out = node_moments(d, nodes)
    g = d["gamma"]; xs0 = np.linalg.solve(g * Sig0, mu0)
    G = np.array([[d["bA"], 1.0], [d["bE"], 0.0]])
    Sig1 = out[0]["Sig1"]                                   # deterministic
    mu_pred = G @ out[0]["m_pred"] - np.array([0.0, d["cE"]])
    pred_move = np.linalg.solve(g * Sig1, mu_pred) - xs0    # predictable part: known at review 0
    innov_moves = np.array([np.linalg.solve(g * Sig1, G @ o["innov"]) for o in out])
    check(np.all([np.allclose(o["Sig1"], Sig1) for o in out]), f"Sigma_1 varies across nodes at phi={phi}")
    for j, o in enumerate(out):
        xs1 = np.linalg.solve(g * o["Sig1"], o["mu1"])
        check(np.allclose(xs1 - xs0, pred_move + innov_moves[j], atol=1e-10), f"decomposition fails at node {j}, phi={phi}")
    mean_innov = prob @ innov_moves
    check(np.max(np.abs(mean_innov)) < 1e-12, f"innovation part not centred at phi={phi}")
    # covariance of the innovation part equals (gamma Sigma_1)^{-1} G phi K (P_0 + R) K' phi G' (gamma Sigma_1)^{-1}
    sf2, sA2, _ = moments(d); R = np.diag([sf2, sA2]); K = out[0]["K"]
    cov_pred = np.linalg.solve(g * Sig1, G) @ (d["phi"] * K @ (P0 + R) @ K.T * d["phi"]) @ np.linalg.solve(g * Sig1, G).T
    cov_emp = (innov_moves * prob[:, None]).T @ innov_moves
    check(np.allclose(cov_emp, cov_pred, atol=1e-12), f"innovation covariance differs from the formula at phi={phi}")
    counts["decomp"] += 1
    print(f"phi={phi}, q_alpha={qa}: predictable target move ({pred_move[0]:+.4f}, {pred_move[1]:+.4f}); innovation sd ({np.sqrt(cov_pred[0,0]):.4f}, {np.sqrt(cov_pred[1,1]):.4f}); P_1 = diag({out[0]['P1'][0,0]:.2e}, {out[0]['P1'][1,1]:.2e}) vs P_0 = diag({P0[0,0]:.2e}, {P0[1,1]:.2e})")

# (ii) the tilt of a lone fund's root band toward the predictable move (coarse regime: innovation support wide against the band)
for phi, thbar_alpha in ((0.5, 0.030), (0.5, -0.020), (0.7, 0.020)):
    d = instance(phi=phi, qalp=0.0, drift_alpha=thbar_alpha - 0.004)
    d["kpA"] = d["kmA"] = 0.002                                 # a narrow band so that the regime is coarse
    nodes, prob = tree(d); mu0, Sig0, m0, P0, out = node_moments(d, nodes)
    g = d["gamma"]; c = g * Sig0[0, 0]
    xs0 = mu0[0] / c
    xs1 = np.array([o["mu1"][0] / (g * o["Sig1"][0, 0]) for o in out])
    U = prob @ (xs1 > xs0 + 1e-12); D = prob @ (xs1 < xs0 - 1e-12)
    tau = d["beta"] * (d["kpA"] * U - d["kmA"] * D) / c
    # root band by scanning the fund incumbent (no ETF, no budget): held iff the dynamic root keeps it
    held = []
    A = np.round(np.arange(max(0.0, xs0 - 0.35), min(1.0, xs0 + 0.35) + 1e-9, 0.005), 6)   # a window around the target
    for a_inc in A:
        d2 = dict(d); d2["a0"] = a_inc
        x0, _, _, _, _ = two_review(d2, mu0, Sig0, out, prob, fund_only=True, no_budget=True)
        held.append(abs(x0[0] - a_inc) < 1e-4)
    held = np.array(held)
    lo, hi = A[held].min(), A[held].max()
    lo_pred, hi_pred = xs0 - d["kpA"] / c + tau, xs0 + d["kmA"] / c + tau
    # coarse regime: every outcome moves the target beyond the static band (check it holds here)
    width = (d["kpA"] + d["kmA"]) / c
    coarse = np.all(np.abs(xs1 - xs0) > width)
    if coarse:
        check(abs(lo - lo_pred) <= 0.006 and abs(hi - hi_pred) <= 0.006, f"tilted band ({lo:.3f},{hi:.3f}) differs from ({lo_pred:.3f},{hi_pred:.3f}) at phi={phi}, alpha_bar={thbar_alpha}")
        counts["tilt"] += 1
    print(f"tilt: phi={phi}, alpha_bar={thbar_alpha}: target {xs0:.3f}, predictable move {np.mean(xs1) - xs0:+.3f}, U={U:.2f} D={D:.2f}, tau={tau:+.4f}, band ({lo:.3f},{hi:.3f}) vs static tilted ({lo_pred:.3f},{hi_pred:.3f}), coarse={coarse}")

# (iii) front-loading of a predictable rise (bought tomorrow in every state) with a slack budget, and the mirror
for thbar_alpha, label in ((0.040, "front"), (-0.030, "back")):
    d = instance(phi=0.5, qalp=0.0, drift_alpha=thbar_alpha - 0.004, tight=False)
    d["a0"] = 0.4 if label == "front" else 0.9; d["p0"] = 0.2
    nodes, prob = tree(d); mu0, Sig0, m0, P0, out = node_moments(d, nodes)
    x0, X1, eta0, eta1, val = two_review(d, mu0, Sig0, out, prob)
    xmy, etamy = one_review(d, mu0, Sig0, np.array([d["a0"], d["p0"]]), d["h0"])
    gA = np.array([o["g"][0] for o in out])
    bought_all = np.all(X1[:, 0] > gA * x0[0] + TOL); sold_all = np.all(X1[:, 0] < gA * x0[0] - TOL)
    if label == "front":
        check(bought_all and eta0 < 1e-6 and np.max(eta1) < 1e-6, f"front-loading instance not as designed (bought_all={bought_all}, eta0={eta0:.1e}, max eta1={np.max(eta1):.1e})")
        check(x0[0] >= xmy[0] - TOL, f"front-loading: dynamic fund {x0[0]:.3f} below myopic {xmy[0]:.3f}")
        counts["front"] += 1
    else:
        check(sold_all and eta0 < 1e-6 and np.max(eta1) < 1e-6, f"mirror instance not as designed (sold_all={sold_all})")
        check(x0[0] <= xmy[0] + TOL, f"mirror: dynamic fund {x0[0]:.3f} above myopic {xmy[0]:.3f}")
        counts["back"] += 1
    print(f"{label}: alpha_bar={thbar_alpha}: myopic fund {xmy[0]:.3f} ETF {xmy[1]:.3f}; dynamic fund {x0[0]:.3f} ETF {x0[1]:.3f}; bought tomorrow everywhere={bought_all}, sold everywhere={sold_all}")

# (iv) transfers: the root clip with alpha~ + S at (m_0, eta_hat_0) and the aggregate no-reserve test on M9's tree
for it in range(6):
    d = instance(tight=(it % 2 == 0), phi=rng.uniform(0.5, 0.95), qlam=rng.uniform(0, 2e-5), qalp=rng.uniform(0, 3e-4), drift_alpha=rng.uniform(-0.01, 0.02))
    d["a0"] = rng.uniform(0.1, 0.5); d["p0"] = rng.uniform(0.0, 0.3)
    nodes, prob = tree(d); mu0, Sig0, m0, P0, out = node_moments(d, nodes)
    x0, X1, eta0, eta1, val = two_review(d, mu0, Sig0, out, prob)
    g = d["gamma"]; beta = d["beta"]; J = len(prob)
    kp = np.array([d["kpA"], d["kpE"]]); km = np.array([d["kmA"], d["kmE"]])
    S = np.zeros(2)
    for j, o in enumerate(out):
        inc = o["g"] * x0; x1 = X1[j]; g1 = o["mu1"] - g * o["Sig1"] @ x1
        for i in range(2):
            t = kp[i] if x1[i] > inc[i] + TOL else (-km[i] if x1[i] < inc[i] - TOL else np.clip((g1[i] - eta1[j]) / (1 + eta1[j]), -km[i], kp[i]))
            S[i] += beta * prob[j] * o["g"][i] * (eta1[j] + (1 + eta1[j]) * t)
    eta_hat = eta0 + beta * prob @ eta1
    sf2, sA2, sE2 = moments(d); sEE = Sig0[1, 1] - sE2; r = Sig0[0, 1] / sEE; v = Sig0[0, 0] - r * r * sEE
    at = mu0[0] - r * mu0[1]; w0 = x0[1] + r * x0[0]; m_0 = mu0[1] - g * sEE * w0
    lo = (at + S[0] + r * m_0 - eta_hat - (1 + eta_hat) * d["kpA"]) / (g * v); hi = (at + S[0] + r * m_0 - eta_hat + (1 + eta_hat) * d["kmA"]) / (g * v)
    clip = np.clip(np.clip(d["a0"], lo, hi), 0.0, d["capA"])
    check(abs(clip - x0[0]) < 5 * TOL, f"transfer: root clip differs on instance {it}: {clip:.4f} vs {x0[0]:.4f}")
    counts["transfer"] += 1
    h0 = d["h0"] - np.sum(x0 - np.array([d["a0"], d["p0"]])) - np.sum(kp * np.maximum(x0 - np.array([d["a0"], d["p0"]]), 0) + km * np.maximum(np.array([d["a0"], d["p0"]]) - x0, 0))
    for j, o in enumerate(out):
        mu1, Sig1 = o["mu1"], o["Sig1"]
        xhat = np.maximum(mu1 - kp, 0) / (g * np.diag(Sig1)); xhatE_s = (mu1[1] + d["kmE"]) / (g * Sig1[1, 1])
        need = np.sum((1 + kp) * np.maximum(xhat - o["g"] * x0, 0)); liq = h0 + (1 - d["kmE"]) * max(o["g"][1] * x0[1] - max(xhatE_s, 0), 0)
        if liq >= need + 1e-9:
            inc = o["g"] * x0; x1 = X1[j]; g1 = mu1 - g * Sig1 @ x1; ok = True
            for i in range(2):
                if x1[i] > inc[i] + TOL: ok &= abs(g1[i] - kp[i]) < MTOL or x1[i] > np.array([d["capA"], d["capE"]])[i] - TOL
                elif x1[i] < inc[i] - TOL: ok &= abs(g1[i] + km[i]) < MTOL or x1[i] < TOL
                else: ok &= (g1[i] <= kp[i] + MTOL) and (x1[i] < TOL or g1[i] >= -km[i] - MTOL)
            check(ok, f"transfer: no-reserve test fails at node {j} on instance {it}")
            counts["noreserve"] += 1

print("cases:", counts)
check(counts["decomp"] >= 4 and counts["tilt"] >= 2 and counts["front"] >= 1 and counts["back"] >= 1 and counts["transfer"] >= 6 and counts["noreserve"] >= 30, "too few instances exercised a part")
if FAIL:
    print(f"{len(FAIL)} check(s) failed"); sys.exit(1)
print("all checks passed")
