"""Claim 112 (D17): the worked learning example in model M8 (one fund, one ETF, cash, two reviews),
and the consistency checks behind it.

It builds the example at the claim's stated inputs, prints the tables the claim quotes, and checks
(exiting non-zero on failure):
 (i)   every gross return under the finite law is positive, so marking keeps holdings nonnegative
       and the funded budget is well defined at both reviews;
 (ii)  the linear filter's error covariance identities hold under the finite law: the belief-mean
       innovation has mean zero and covariance V_0 = P_0 - P_1 over the tree, and P_1 is the
       information-form value; and the exact finite-law posterior mean differs from the filter's
       mean at some public node while agreeing with it in expectation (the resolution of part 1);
 (iii) the two-review dynamic program is consistent: its value at review 0 is at least the value of
       the myopic policy evaluated on the same tree, and the review-1 problem is solved by the
       one-fund one-ETF rule (claim 110's), checked against a grid at every public node.
A check and a worked example, not a proof. Run: uv run python checks/112/check.py
"""
import sys
import itertools
import numpy as np

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


# ---------------------------------------------------------------- inputs (the claim's table 1)
INP = dict(
    bA=0.9, bE=1.0,                     # factor loadings (one factor)
    cE=0.0005,                          # ETF drag per quarter (5 bp)
    lam0=0.010, s_lam=0.004,            # prior mean and sd of the factor premium (per quarter)
    alp0=0.004, s_alp=0.020,            # prior mean and sd of the fund's net alpha (per quarter)
    zf=(-0.084, -0.076, 0.076, 0.084),  # factor shock law (equiprobable): sd 0.0801
    zA=(-0.08, -0.04, 0.04, 0.08),      # fund residual law (equiprobable): sd 0.0632
    zE=(-0.005, 0.005),                 # ETF residual law (equiprobable): sd 0.005
    gamma=2.5, beta=1.0,
    kpA=0.005, kmA=0.005, kpE=0.001, kmE=0.001,   # rates: fund 50 bp, ETF 10 bp each way
    capA=1.0, capE=1.0,
    a0=0.40, p0=0.00, h0=0.06,          # incumbents: fund 0.40, ETF 0 (at zero), cash 0.06
)


def moments(inp):
    sf2 = np.mean(np.square(inp["zf"])); sA2 = np.mean(np.square(inp["zA"])); sE2 = np.mean(np.square(inp["zE"]))
    return sf2, sA2, sE2


def filter_step(inp, plam, palp, sf2, sA2):
    """Scalar Kalman updates for the two blocks (block-diagonal Sigma_z, zero prior cross-covariance)."""
    klam = plam / (plam + sf2); kalp = palp / (palp + sA2)
    return klam, kalp, plam - klam * plam, palp - kalp * palp


def predictive(inp, lam, alp, plam, palp, sf2, sA2, sE2):
    bA, bE = inp["bA"], inp["bE"]
    mu = np.array([bA * lam + alp, bE * lam - inp["cE"]])
    Sig = np.array([[bA * bA * (sf2 + plam) + sA2 + palp, bA * bE * (sf2 + plam)],
                    [bA * bE * (sf2 + plam), bE * bE * (sf2 + plam) + sE2]])
    return mu, Sig


# ---------------------------------------------------------------- one review, one fund, one ETF, cash (claim 110's rule, vectorized)
def solve_one_review(inp, mu, Sig, a_inc, p_inc, h_inc, it=50):
    """Vectorized over incumbents. Returns post-trade (a, p), cash, the score, eta and the ETF's status."""
    a_inc = np.asarray(a_inc, float); p_inc = np.asarray(p_inc, float); h_inc = np.asarray(h_inc, float)
    g = inp["gamma"]; kpA, kmA, kpE, kmE = inp["kpA"], inp["kmA"], inp["kpE"], inp["kmE"]
    v = Sig[0, 0] - Sig[0, 1] ** 2 / Sig[1, 1] * 0 + 0.0     # placeholder, replaced below
    # claim 110's coordinates: r = Sigma_AE/Sigma_EE (netting weight when the ETF spans the factor: bA/bE), muE, sEE, sE, v
    bA, bE = inp["bA"], inp["bE"]; r = bA / bE
    sf2, sA2, sE2 = moments(inp)
    # Sig = gamma-free covariance here; the claim's sigma_EE = bE^2 (sf2 + plam), sigma_E = sE2, v = sA2 + palp
    sEE = Sig[1, 1] - sE2; sE = sE2; v = Sig[0, 0] - r * r * sEE
    muE = mu[1]; at = mu[0] - r * (muE)         # alpha~ = alpha_hat + r c^E  (mu_A = bA lam + alp = r muE + alpha~ ... exact: alpha~ = mu_A - r mu_E)
    xbar = inp["capA"]

    def funds_at(m, eta):
        lo = (at + r * m - eta - (1 + eta) * kpA) / (g * v)
        hi = (at + r * m - eta + (1 + eta) * kmA) / (g * v)
        return np.clip(np.clip(a_inc, lo, hi), 0.0, xbar)

    def p_of(m, eta):
        return (muE - m) / (g * sEE) - r * funds_at(m, eta)

    def root(f, lo, hi):
        lo = np.full_like(a_inc, lo); hi = np.full_like(a_inc, hi)
        for _ in range(it):
            mid = 0.5 * (lo + hi); pos = f(mid) > 0
            lo = np.where(pos, mid, lo); hi = np.where(pos, hi, mid)
        return 0.5 * (lo + hi)

    def etf_and_funds(eta):
        thr_b = eta + (1 + eta) * kpE; thr_s = eta - (1 + eta) * kmE
        m0 = root(lambda m: p_of(m, eta), -1.0, 1.0)
        mI = root(lambda m: p_of(m, eta) - p_inc, -1.0, 1.0)
        gI = mI - g * sE * p_inc
        trad = lambda thr: root(lambda m: -(m - g * sE * p_of(m, eta) - thr), -1.0, 1.0)
        mB, mS = trad(thr_b), trad(thr_s)
        zero_inc = p_inc < 1e-12
        # statuses: from zero: Z if m0 <= thr_b else B; from p_inc > 0: B if gI > thr_b, S/Z if gI < thr_s, else I
        st = np.where(zero_inc, np.where(m0 <= thr_b, 0, 1), np.where(gI > thr_b, 1, np.where(gI < thr_s, np.where(m0 <= thr_s, 0, 2), 3)))
        m = np.select([st == 0, st == 1, st == 2, st == 3], [m0, mB, mS, mI])
        a = funds_at(m, eta)
        p = np.select([st == 0, st == 1, st == 2, st == 3], [np.zeros_like(m), p_of(mB, eta), p_of(mS, eta), p_inc])
        p = np.clip(p, 0.0, inp["capE"])
        return a, p, m, st

    def cash_after(a, p):
        ua, up = a - a_inc, p - p_inc
        return h_inc - ua - up - kpA * np.maximum(ua, 0) - kmA * np.maximum(-ua, 0) - kpE * np.maximum(up, 0) - kmE * np.maximum(-up, 0)

    a0, p0, m0_, st0 = etf_and_funds(np.zeros_like(a_inc))
    slack = cash_after(a0, p0) >= -1e-12
    # eta by bisection where the budget binds (the cash slack is nondecreasing in eta)
    lo = np.zeros_like(a_inc); hi = np.full_like(a_inc, 5.0)
    for _ in range(it):
        mid = 0.5 * (lo + hi); a_, p_, _, _ = etf_and_funds(mid)
        neg = cash_after(a_, p_) < 0
        lo = np.where(neg, mid, lo); hi = np.where(neg, hi, mid)
    eta = np.where(slack, 0.0, 0.5 * (lo + hi))
    a, p, m, st = etf_and_funds(eta)
    a = np.where(slack, a0, a); p = np.where(slack, p0, p); m = np.where(slack, m0_, m); st = np.where(slack, st0, st)
    h = cash_after(a, p)
    x = np.stack([a, p], -1)
    score = x @ mu - 0.5 * g * np.einsum("...i,ij,...j->...", x, Sig, x) - (h_inc - h - (a - a_inc) - (p - p_inc))
    return a, p, h, score, eta, m, st


def score_of(inp, mu, Sig, a, p, a_inc, p_inc):
    ua, up = a - a_inc, p - p_inc
    cost = inp["kpA"] * np.maximum(ua, 0) + inp["kmA"] * np.maximum(-ua, 0) + inp["kpE"] * np.maximum(up, 0) + inp["kmE"] * np.maximum(-up, 0)
    x = np.stack([a, p], -1)
    return x @ mu - 0.5 * inp["gamma"] * np.einsum("...i,ij,...j->...", x, Sig, x) - cost, cost


# ---------------------------------------------------------------- the tree (finite-law variant)
def tree(inp):
    """Hidden branches (lambda, alpha, zf, zA, zE) at review 1, equiprobable; public observation y_1 = (f, rA, rE)."""
    lams = (inp["lam0"] - inp["s_lam"], inp["lam0"] + inp["s_lam"])
    alps = (inp["alp0"] - inp["s_alp"], inp["alp0"] + inp["s_alp"])
    rows = []
    for lam, alp, zf, zA, zE in itertools.product(lams, alps, inp["zf"], inp["zA"], inp["zE"]):
        f = lam + zf; rA = inp["bA"] * f + alp + zA; rE = inp["bE"] * f - inp["cE"] + zE
        rows.append((lam, alp, f, rA, rE))
    rows = np.array(rows)
    prob = np.full(len(rows), 1.0 / len(rows))
    return rows, prob


def main():
    inp = INP; g = inp["gamma"]; bA, bE = inp["bA"], inp["bE"]
    sf2, sA2, sE2 = moments(inp)
    plam0, palp0 = inp["s_lam"] ** 2, inp["s_alp"] ** 2
    klam, kalp, plam1, palp1 = filter_step(inp, plam0, palp0, sf2, sA2)
    # information form check
    check(abs(1 / plam1 - (1 / plam0 + 1 / sf2)) < 1e-9 and abs(1 / palp1 - (1 / palp0 + 1 / sA2)) < 1e-9, "information-form P_1 fails")
    mu0, Sig0 = predictive(inp, inp["lam0"], inp["alp0"], plam0, palp0, sf2, sA2, sE2)
    xstar0 = np.linalg.solve(g * Sig0, mu0)
    print("== Table 1: inputs (per quarter) ==")
    print(f"loadings b_A={bA}, b_E={bE}; drag c^E={inp['cE']}; prior lambda ~ ({inp['lam0']}, sd {inp['s_lam']}), alpha ~ ({inp['alp0']}, sd {inp['s_alp']})")
    print(f"shock sds: factor {np.sqrt(sf2):.4f}, fund residual {np.sqrt(sA2):.4f}, ETF residual {np.sqrt(sE2):.4f}; gamma={g}; rates fund {inp['kpA']}/{inp['kmA']}, ETF {inp['kpE']}/{inp['kmE']}")
    print(f"incumbents: fund {inp['a0']}, ETF {inp['p0']}, cash {inp['h0']}; caps {inp['capA']}, {inp['capE']}; two reviews, beta={inp['beta']}")
    print("== Table 2: beliefs and predictive moments at review 0 ==")
    print(f"P_0 = diag({plam0:.2e}, {palp0:.2e}); Kalman gains k_lambda={klam:.4f}, k_alpha={kalp:.4f}; P_1 = diag({plam1:.3e}, {palp1:.3e})")
    print(f"mu_0 = ({mu0[0]:.5f}, {mu0[1]:.5f}); Sigma_0 = [[{Sig0[0,0]:.5f}, {Sig0[0,1]:.5f}], [., {Sig0[1,1]:.5f}]]; target x*_0 = ({xstar0[0]:.4f}, {xstar0[1]:.4f})")

    # (i) positive gross returns and the tree
    rows, prob = tree(inp)
    check(np.all(1 + rows[:, 3] > 0) and np.all(1 + rows[:, 4] > 0), "a gross return is not positive under the finite law")
    # public nodes: distinct (f, rA, rE)
    keys = np.round(rows[:, 2:5], 10)
    uniq, inv = np.unique(keys, axis=0, return_inverse=True)
    inv = inv.ravel()
    pub_prob = np.bincount(inv, weights=prob)
    n_pub = len(uniq)
    # filter means at each public node
    f1 = uniq[:, 0]; s1 = uniq[:, 1] - bA * f1
    lam1 = inp["lam0"] + klam * (f1 - inp["lam0"]); alp1 = inp["alp0"] + kalp * (s1 - inp["alp0"])
    # exact finite-law posterior means at each public node
    post_lam = np.bincount(inv, weights=prob * rows[:, 0]) / pub_prob
    post_alp = np.bincount(inv, weights=prob * rows[:, 1]) / pub_prob
    # (ii) innovation identities
    eps = np.stack([lam1 - inp["lam0"], alp1 - inp["alp0"]], 1)
    mean_eps = pub_prob @ eps
    cov_eps = (eps * pub_prob[:, None]).T @ eps
    check(np.max(np.abs(mean_eps)) < 1e-12, "innovation mean is not zero")
    check(abs(cov_eps[0, 0] - (plam0 - plam1)) < 1e-12 and abs(cov_eps[1, 1] - (palp0 - palp1)) < 1e-12, "innovation covariance differs from V_0 = P_0 - P_1")
    gap = np.stack([post_lam - lam1, post_alp - alp1], 1)
    check(np.max(np.abs(pub_prob @ gap)) < 1e-12, "posterior and filter means differ in expectation")
    check(np.max(np.abs(gap)) > 1e-4, "posterior and filter means coincide at every node (no gap to show)")
    print("== Table 3: review 1 beliefs, filter against the exact finite-law posterior ==")
    print(f"public nodes: {n_pub}; largest |posterior - filter| gap: lambda {np.max(np.abs(gap[:,0])):.4f}, alpha {np.max(np.abs(gap[:,1])):.4f}; both zero in expectation")
    # two illustrative nodes: A, an ambiguous observation (f_1 = lambda_0 + 0.080, residual alpha_0 + 0.06, both from two hidden
    # branches); B, a revealing one (f_1 = lambda_0 + 0.088, residual alpha_0 + 0.10); the ETF residual +0.005 in both
    def pick(f_t, s_t, e_t):
        return int(np.argmin((f1 - f_t) ** 2 + (s1 - s_t) ** 2 + (uniq[:, 2] - (bE * f_t - inp["cE"] + e_t)) ** 2))
    i_hi = pick(inp["lam0"] + 0.080, inp["alp0"] + 0.06, 0.005); i_lo = pick(inp["lam0"] + 0.088, inp["alp0"] + 0.10, 0.005)
    for name, i in (("A, ambiguous", i_hi), ("B, revealing", i_lo)):
        print(f"  node ({name}): f_1={f1[i]:+.3f}, r^A_1-b_A f_1={s1[i]:+.3f}; filter (lambda_1, alpha_1)=({lam1[i]:.5f}, {alp1[i]:.5f}); exact posterior=({post_lam[i]:.5f}, {post_alp[i]:.5f}); prob {pub_prob[i]:.4f}")

    # (iii) decisions: myopic at review 0
    a_m, p_m, h_m, sc_m, eta_m, m_m, st_m = solve_one_review(inp, mu0, Sig0, [inp["a0"]], [inp["p0"]], [inp["h0"]])
    # dynamic: grid over review-0 actions, exact review-1 solve at every public node
    da = 0.02
    A = np.round(np.arange(0.0, inp["capA"] + da / 2, da), 10); P = np.round(np.arange(0.0, inp["capE"] + da / 2, da), 10)
    AA, PP = np.meshgrid(A, P, indexing="ij")
    # candidate actions: the grid plus the myopic action itself (so the comparison is exact, not grid-limited)
    # plus a fine local grid (step 0.002) around the myopic action, for small deviations such as keeping cash
    dl = 0.002; loc = np.arange(-0.06, 0.06 + dl / 2, dl)
    LA, LP = np.meshgrid(np.clip(a_m[0] + loc, 0, inp["capA"]), np.clip(p_m[0] + loc, 0, inp["capE"]), indexing="ij")
    a_act = np.concatenate([AA.ravel(), LA.ravel(), [a_m[0]]]); p_act = np.concatenate([PP.ravel(), LP.ravel(), [p_m[0]]])
    sc0, cost0 = score_of(inp, mu0, Sig0, a_act, p_act, inp["a0"], inp["p0"])
    h_act = inp["h0"] - (a_act - inp["a0"]) - (p_act - inp["p0"]) - cost0
    h_act[-1] = max(h_act[-1], 0.0)
    feas = h_act >= -1e-12
    # review-1 moments are the same at every node (P_1 deterministic); the means differ
    cont = np.zeros(len(a_act))
    for j in range(n_pub):
        mu1, Sig1 = predictive(inp, lam1[j], alp1[j], plam1, palp1, sf2, sA2, sE2)
        gA, gE = 1 + uniq[j, 1], 1 + uniq[j, 2]
        _, _, _, sc1, _, _, _ = solve_one_review(inp, mu1, Sig1, a_act * gA, p_act * gE, h_act)
        cont += pub_prob[j] * sc1
    total = np.where(feas, sc0 + inp["beta"] * cont, -np.inf)
    k = int(np.argmax(total)); a_d, p_d, h_d = a_act[k], p_act[k], h_act[k]
    # the myopic policy's value on the same tree (its own review-0 action, then the review-1 rule at every node)
    hm = max(float(h_m[0]), 0.0); cont_m = 0.0
    for j in range(n_pub):
        mu1, Sig1 = predictive(inp, lam1[j], alp1[j], plam1, palp1, sf2, sA2, sE2)
        gA, gE = 1 + uniq[j, 1], 1 + uniq[j, 2]
        _, _, _, sc1, _, _, _ = solve_one_review(inp, mu1, Sig1, [a_m[0] * gA], [p_m[0] * gE], [hm])
        cont_m += pub_prob[j] * sc1[0]
    value_m = float(sc_m[0]) + inp["beta"] * cont_m
    check(total[k] >= value_m - 1e-9, "dynamic value below the myopic policy's value")
    # review-1 rule against a grid at every public node from the dynamic action
    worst = 0.0
    for j in range(n_pub):
        mu1, Sig1 = predictive(inp, lam1[j], alp1[j], plam1, palp1, sf2, sA2, sE2)
        gA, gE = 1 + uniq[j, 1], 1 + uniq[j, 2]
        ai, pi_, hi_ = a_d * gA, p_d * gE, h_d
        a1, p1, h1, sc1, eta1, m1, st1 = solve_one_review(inp, mu1, Sig1, [ai], [pi_], [hi_])
        s_grid, c_grid = score_of(inp, mu1, Sig1, a_act, p_act, ai, pi_)
        ok = (hi_ - (a_act - ai) - (p_act - pi_) - c_grid) >= -1e-12
        best = np.max(np.where(ok, s_grid, -np.inf))
        worst = max(worst, best - sc1[0])
    check(worst < 2e-6, f"review-1 rule below the grid optimum by {worst:.2e}")
    print("== Table 4: today's decision at review 0 ==")
    rho = Sig0[0, 1] / Sig0[1, 1]; v_res = Sig0[0, 0] - Sig0[0, 1] ** 2 / Sig0[1, 1]; at_rho = mu0[0] - rho * mu0[1]
    gA0 = mu0[0] - g * (Sig0[0, 0] * inp["a0"] + Sig0[0, 1] * p_m[0])
    print(f"myopic (one review): fund {a_m[0]:.3f}, ETF {p_m[0]:.3f}, cash {h_m[0]:.3f}; eta={eta_m[0]:.4f}; ETF status {['at zero','bought','sold','idle'][st_m[0]]}; exposure price m={m_m[0]:.5f}")
    print(f"   fund marginal at the optimum {gA0:.5f} = alpha~ {at_rho:.5f} + rho {rho:.4f} x g_E {mu0[1] - g * (Sig0[1,1] * p_m[0] + Sig0[0,1] * inp['a0']):.5f} - gamma v {v_res:.5f} x a {inp['a0']}; purchase line {eta_m[0] + (1 + eta_m[0]) * inp['kpA']:.5f}")
    print(f"dynamic (two reviews, grid {da} plus a local grid of step {dl} around the myopic action): fund {a_d:.3f}, ETF {p_d:.3f}, cash {h_d:.3f}; value {total[k]:.6f} against the myopic policy's {value_m:.6f} (gain {1e4*(total[k]-value_m):.2f} bp of wealth over the two quarters)")
    # review-1 decisions at the two illustrative nodes from the dynamic action
    print("== Table 5: review 1 decisions from the dynamic action ==")
    for name, i in (("A, ambiguous", i_hi), ("B, revealing", i_lo)):
        mu1, Sig1 = predictive(inp, lam1[i], alp1[i], plam1, palp1, sf2, sA2, sE2)
        gA, gE = 1 + uniq[i, 1], 1 + uniq[i, 2]
        ai, pi_, hi_ = a_d * gA, p_d * gE, h_d
        a1, p1, h1, sc1, eta1, m1, st1 = solve_one_review(inp, mu1, Sig1, [ai], [pi_], [hi_])
        xs1 = np.linalg.solve(g * Sig1, mu1)
        print(f"  node ({name}): marked holdings fund {ai:.3f}, ETF {pi_:.3f}, cash {hi_:.3f}; mu_1=({mu1[0]:.5f}, {mu1[1]:.5f}); target ({xs1[0]:.3f}, {xs1[1]:.3f}); trade to fund {a1[0]:.3f}, ETF {p1[0]:.3f}, cash {h1[0]:.3f}; eta={eta1[0]:.4f}; ETF {['at zero','bought','sold','idle'][st1[0]]}")
        # a manager using the exact finite-law posterior mean instead (same Sigma_1): the nonlinear-filter comparison
        muB, _ = predictive(inp, post_lam[i], post_alp[i], plam1, palp1, sf2, sA2, sE2)
        aB, pB, hB, scB, etaB, mB, stB = solve_one_review(inp, muB, Sig1, [ai], [pi_], [hi_])
        # its trade scored under the true finite-law conditional moments (the posterior mean; the score's Sigma_1 kept)
        sc_true_filter, _ = score_of(inp, muB, Sig1, a1, p1, ai, pi_)
        print(f"     exact-posterior manager at this node: mu^B_1=({muB[0]:.5f}, {muB[1]:.5f}); trade to fund {aB[0]:.3f}, ETF {pB[0]:.3f}; its stage score {scB[0]:.5f} against the filter manager's {sc_true_filter[0]:.5f} under the posterior mean")
    # ---- Table 6: the exact-posterior (nonlinear-filter) manager beside the filter manager, on the same tree
    # Common yardstick: the true finite-law conditional moments at review 1 are the posterior's, so every policy is
    # scored at review 1 with the posterior-moment score; review 0's score is common (the prior is shared).
    post_plam = np.bincount(inv, weights=prob * rows[:, 0] ** 2) / pub_prob - post_lam ** 2
    post_palp = np.bincount(inv, weights=prob * rows[:, 1] ** 2) / pub_prob - post_alp ** 2
    def node_moments_B(j):
        return predictive(inp, post_lam[j], post_alp[j], max(post_plam[j], 0.0), max(post_palp[j], 0.0), sf2, sA2, sE2)
    def review1_values(a_act_, p_act_, h_act_, manager):
        """expected review-1 posterior-moment score of the manager's review-1 policy from the given review-0 actions."""
        cont = np.zeros(len(a_act_))
        for j in range(n_pub):
            muB, SigB = node_moments_B(j)
            gA, gE = 1 + uniq[j, 1], 1 + uniq[j, 2]
            ai, pi_ = a_act_ * gA, p_act_ * gE
            if manager == "B":
                a1, p1, _, _, _, _, _ = solve_one_review(inp, muB, SigB, ai, pi_, h_act_)
            else:
                mu1, Sig1 = predictive(inp, lam1[j], alp1[j], plam1, palp1, sf2, sA2, sE2)
                a1, p1, _, _, _, _, _ = solve_one_review(inp, mu1, Sig1, ai, pi_, h_act_)
            sc, _ = score_of(inp, muB, SigB, a1, p1, ai, pi_)
            cont += pub_prob[j] * sc
        return cont
    contF = review1_values(a_act, p_act, np.maximum(h_act, 0.0), "F"); contB = review1_values(a_act, p_act, np.maximum(h_act, 0.0), "B")
    totF = np.where(feas, sc0 + inp["beta"] * contF, -np.inf); totB = np.where(feas, sc0 + inp["beta"] * contB, -np.inf)
    kF, kB = int(np.argmax(totF)), int(np.argmax(totB))
    # myopic policies of both managers: the same review-0 action (common prior), then each manager's review-1 rule
    vF_my = float(sc_m[0]) + inp["beta"] * review1_values(np.array([a_m[0]]), np.array([p_m[0]]), np.array([hm]), "F")[0]
    vB_my = float(sc_m[0]) + inp["beta"] * review1_values(np.array([a_m[0]]), np.array([p_m[0]]), np.array([hm]), "B")[0]
    check(totB[kB] >= totF[kF] - 1e-12 and vB_my >= vF_my - 1e-12, "the exact-posterior manager scores below the filter manager under the posterior yardstick")
    print("== Table 6: the exact-posterior manager beside the filter manager (posterior-moment yardstick) ==")
    print(f"myopic: filter manager value {vF_my:.6f}, exact-posterior manager {vB_my:.6f}; the nonlinear filter gains {1e4*(vB_my-vF_my):.2f} bp of wealth over two quarters")
    print(f"dynamic: filter manager review-0 action fund {a_act[kF]:.3f}, ETF {p_act[kF]:.3f} (value {totF[kF]:.6f}); exact-posterior manager fund {a_act[kB]:.3f}, ETF {p_act[kB]:.3f} (value {totB[kB]:.6f}); gain {1e4*(totB[kB]-totF[kF]):.2f} bp")
    nd = 0
    for j in range(n_pub):
        muB, SigB = node_moments_B(j); mu1, Sig1 = predictive(inp, lam1[j], alp1[j], plam1, palp1, sf2, sA2, sE2)
        gA, gE = 1 + uniq[j, 1], 1 + uniq[j, 2]
        aF, pF, _, _, _, _, _ = solve_one_review(inp, mu1, Sig1, [a_d * gA], [p_d * gE], [h_d])
        aB, pB, _, _, _, _, _ = solve_one_review(inp, muB, SigB, [a_d * gA], [p_d * gE], [h_d])
        nd += int(abs(aF[0] - aB[0]) > 1e-4 or abs(pF[0] - pB[0]) > 1e-4)
    print(f"review-1 decisions from the common review-0 action differ between the two managers at {nd} of {n_pub} public nodes")
    for name, i in (("A, ambiguous", i_hi), ("B, revealing", i_lo)):
        muB, SigB = node_moments_B(i); gA, gE = 1 + uniq[i, 1], 1 + uniq[i, 2]
        aB, pB, hB, _, etaB, _, stB = solve_one_review(inp, muB, SigB, [a_d * gA], [p_d * gE], [h_d])
        print(f"  node ({name}): exact-posterior manager mu^B_1=({muB[0]:.5f}, {muB[1]:.5f}), posterior sds ({np.sqrt(max(post_plam[i],0)):.4f}, {np.sqrt(max(post_palp[i],0)):.4f}); trade to fund {aB[0]:.3f}, ETF {pB[0]:.3f}, cash {hB[0]:.3f}; eta={etaB[0]:.4f}; ETF {['at zero','bought','sold','idle'][stB[0]]}")
    if FAIL:
        print(f"{len(FAIL)} check(s) failed"); sys.exit(1)
    print("all checks passed")


if __name__ == "__main__":
    main()
