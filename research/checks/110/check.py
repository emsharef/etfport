"""Solver checks of claim 110 (M7, one review, one ETF and N funds): the optimum through two monotone
scalars, the exposure price m and the cash price eta; the ETF's status by thresholds; every fund's
trade as its one-fund clip at (m, eta).

Random assumed instances; the claim's scalar rule (bisection on m per regime, then on eta) is
compared with cvxpy/CLARABEL on the joint problem (floating point, not a certificate). Exits
non-zero on failure. A check, not a proof. Run: uv run python checks/110/check.py
"""
import sys
import numpy as np
import cvxpy as cp

rng = np.random.default_rng(110)
FAIL = []
TOL = 3e-4


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


def instance(N=4, sigE=False, tight=False, pzero=False, wide=False):
    K = 1
    BA = rng.uniform(-0.6, 1.5, (N, K))
    BE = np.array([[rng.uniform(0.7, 1.3)]])
    Sf = np.array([[rng.uniform(0.003, 0.012)]])
    v = rng.uniform(0.0005, 0.004, N)
    SE = np.array([rng.uniform(0.0, 0.0004)]) if sigE else np.zeros(1)
    cE = np.array([rng.uniform(-0.0005, 0.0015)])
    lam = np.array([rng.uniform(-0.01, 0.03)])
    alpha = rng.uniform(-0.01, 0.015, N)
    kpA = rng.uniform(0.0, 0.01, N); kmA = rng.uniform(0.0, 0.01, N)
    kE = 0.006 if wide else 0.002                              # ETF rates up to 20 bp, or 60 bp on the wide-band instances
    kpE = np.array([rng.uniform(0.0, kE)]); kmE = np.array([rng.uniform(0.0, kE)])
    gamma = rng.uniform(2.0, 6.0)
    B = np.vstack([BA, BE])
    gSig = gamma * (B @ Sf @ B.T + np.diag(np.concatenate([v, SE])))
    mu = np.concatenate([alpha + BA @ lam, BE @ lam - cE])
    xmE = np.array([0.0 if (pzero or rng.uniform() < 0.4) else rng.uniform(0.0, 1.5)])
    xm = np.concatenate([rng.uniform(0.0, 0.5, N), xmE])
    xbarA = np.full(N, rng.uniform(0.3, 5.0))
    h = rng.uniform(0.0, 0.03) if tight else 100.0
    R = np.linalg.inv(BE); r = (R.T @ BA.T).ravel()          # netting weights r_i
    return dict(N=N, BA=BA, BE=BE, Sf=Sf, v=v, SE=float(SE[0]), cE=float(cE[0]), lam=lam, alpha=alpha,
                kp=np.concatenate([kpA, kpE]), km=np.concatenate([kmA, kmE]), gamma=gamma, gSig=gSig, mu=mu,
                xm=xm, xbarA=xbarA, h=h, r=r, sEE=float((BE @ Sf @ BE.T)[0, 0]), muE=float((BE @ lam - cE)[0]),
                at=alpha + r * float(cE[0]))


def solve(d):
    n = d["N"] + 1; N = d["N"]
    x = cp.Variable(n); u = x - d["xm"]
    cost = cp.sum(cp.multiply(d["kp"], cp.pos(u)) + cp.multiply(d["km"], cp.pos(-u)))
    obj = d["mu"] @ x - 0.5 * cp.quad_form(x, cp.psd_wrap(d["gSig"])) - cost
    budget = d["h"] - cp.sum(u) - cost >= 0
    p = cp.Problem(cp.Maximize(obj), [x >= 0, x[:N] <= d["xbarA"], budget]); p.solve(solver=cp.CLARABEL)
    return np.array(x.value).ravel(), float(budget.dual_value)


# ---- the claim's scalar rule ---------------------------------------------------------------
def funds_at(d, m, eta):
    """part 1: every fund's clip at the exposure price m and cash price eta."""
    N = d["N"]; g = d["gamma"]
    lo = (d["at"] + d["r"] * m - eta - (1 + eta) * d["kp"][:N]) / (g * d["v"])
    hi = (d["at"] + d["r"] * m - eta + (1 + eta) * d["km"][:N]) / (g * d["v"])
    return np.clip(np.clip(d["xm"][:N], lo, hi), 0.0, d["xbarA"])


def q_of(d, m, eta):
    return float(d["r"] @ funds_at(d, m, eta))


def root(f, lo, hi, it=70):
    """root of a function that changes sign from positive at lo to negative at hi (monotone), by bisection."""
    for _ in range(it):
        mid = 0.5 * (lo + hi)
        if f(mid) > 0:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def etf_and_funds(d, eta):
    """parts 2 and 5: the ETF's status and the exposure price m given eta, then the holdings.
    With Sigma_E > 0 the traded regimes solve m - gamma sigma_E p(m) = threshold (part 5)."""
    g = d["gamma"]; sEE = d["sEE"]; sE = d["SE"]; muE = d["muE"]; pm = d["xm"][d["N"]]
    kpE, kmE = d["kp"][d["N"]], d["km"][d["N"]]
    w_of = lambda m: (muE - m) / (g * sEE)                       # exposure at price m
    p_of = lambda m: w_of(m) - q_of(d, m, eta)                    # the ETF holding at price m, strictly decreasing
    thr_b = eta + (1 + eta) * kpE; thr_s = eta - (1 + eta) * kmE
    M0, M1 = -1.0, 1.0                                            # bracket for m (marginals are O(1e-2))
    m0 = root(lambda m: p_of(m), M0, M1)                          # at-zero candidate: p(m) = 0
    traded = lambda thr: root(lambda m: -(m - g * sE * p_of(m) - thr), M0, M1)   # m - gamma sigma_E p(m) = thr
    if pm < 1e-12:
        if m0 <= thr_b:
            m, status = m0, "Z"
        else:
            m, status = traded(thr_b), "B"
    else:
        mI = root(lambda m: w_of(m) - pm - q_of(d, m, eta), M0, M1)   # idle candidate: p(m) = p^-
        gI = mI - g * sE * pm                                     # the ETF's marginal when idle
        if gI > thr_b:
            m, status = traded(thr_b), "B"
        elif gI < thr_s:
            if m0 <= thr_s:                                       # the sale reaches zero
                m, status = m0, "Z"
            else:
                m, status = traded(thr_s), "S"
        else:
            m, status = mI, "I"
    xA = funds_at(d, m, eta)
    p = pm if status == "I" else (0.0 if status == "Z" else p_of(m))
    return np.concatenate([xA, [p]]), m, status


def cash_slack(d, x):
    u = x - d["xm"]
    return d["h"] - np.sum(u) - np.sum(d["kp"] * np.maximum(u, 0) + d["km"] * np.maximum(-u, 0))


def rule(d):
    """part 3: eta = 0 if the budget is slack there, else the root of the nondecreasing cash slack."""
    x0, m0, s0 = etf_and_funds(d, 0.0)
    if cash_slack(d, x0) >= -1e-12:
        return x0, 0.0, m0, s0
    eta = root(lambda e: -cash_slack(d, etf_and_funds(d, e)[0]), 0.0, 5.0)
    x, m, s = etf_and_funds(d, eta)
    return x, eta, m, s


counts = dict(n=0, Z=0, B=0, S=0, I=0, tight=0, fromzero=0, bdir=0, sigE=0)
for it in range(360):
    d = instance(N=rng.integers(2, 6), sigE=(it % 3 == 2), tight=(it % 2 == 0), pzero=(it % 5 == 0), wide=(it % 4 == 1))
    x_s, eta_s = solve(d)
    x_r, eta_r, m_r, status = rule(d)
    N = d["N"]
    check(np.max(np.abs(x_r - x_s)) < 5 * TOL, f"holdings differ from the solver on instance {it} (status {status}, eta {eta_r:.4f}): max diff {np.max(np.abs(x_r - x_s)):.2e}")
    check(abs(eta_r - eta_s) < 2e-3 or np.max(np.abs(x_r - x_s)) < 5 * TOL, f"eta differs on instance {it}: {eta_r:.4f} vs {eta_s:.4f}")
    # the exposure price at the solver's optimum
    m_sol = d["muE"] - d["gamma"] * d["sEE"] * (x_s[N] + float(d["r"] @ x_s[:N]))
    check(abs(m_sol - m_r) < 5e-4, f"exposure price differs on instance {it}: {m_r:.5f} vs {m_sol:.5f} (status {status})")
    # every fund's marginal at the solver's optimum is alpha~ + r m - gamma v x
    gsol = d["mu"] - d["gSig"] @ x_s
    check(np.max(np.abs(gsol[:N] - (d["at"] + d["r"] * m_sol - d["gamma"] * d["v"] * x_s[:N]))) < 1e-6, f"fund marginal identity fails on instance {it}")
    # part 4: the fund's direction from the incumbent at the optimum's (m, eta)
    for i in range(N):
        gi = d["at"][i] + d["r"][i] * m_r - d["gamma"] * d["v"][i] * d["xm"][i]
        if gi > eta_r + (1 + eta_r) * d["kp"][i] + 1e-6 and d["xm"][i] < d["xbarA"][i] - TOL:
            check(x_s[i] > d["xm"][i] + TOL, f"part 4: fund {i} should be bought on instance {it}")
            counts["bdir"] += 1
        if gi < eta_r - (1 + eta_r) * d["km"][i] - 1e-6 and d["xm"][i] > TOL:
            check(x_s[i] < d["xm"][i] - TOL, f"part 4: fund {i} should be sold on instance {it}")
            counts["bdir"] += 1
    counts["n"] += 1; counts[status] += 1; counts["tight"] += int(eta_s > 1e-5); counts["fromzero"] += int(d["xm"][N] < 1e-12); counts["sigE"] += int(d["SE"] > 0)

# part 5 identities: with ETF residual risk the funds' exposure-price identity holds and the ETF's line shifts by gamma sigma_E p
n5 = 0
for it in range(60):
    d = instance(N=3, sigE=True, tight=(it % 2 == 0))
    x_s, eta_s = solve(d); N = d["N"]
    m_sol = d["muE"] - d["gamma"] * d["sEE"] * (x_s[N] + float(d["r"] @ x_s[:N]))
    gsol = d["mu"] - d["gSig"] @ x_s
    check(np.max(np.abs(gsol[:N] - (d["at"] + d["r"] * m_sol - d["gamma"] * d["v"] * x_s[:N]))) < 1e-6, f"part 5: fund marginal identity fails with Sigma_E on instance {it}")
    check(abs(gsol[N] - (m_sol - d["gamma"] * d["SE"] * x_s[N])) < 1e-6, f"part 5: ETF line fails with Sigma_E on instance {it}")
    n5 += 1

print("cases:", counts, "sigmaE:", n5)
check(min(counts["Z"], counts["B"], counts["S"], counts["I"]) >= 8 and counts["tight"] >= 30 and counts["bdir"] >= 30, "too few instances exercised a status")
if FAIL:
    print(f"{len(FAIL)} check(s) failed"); sys.exit(1)
print("all checks passed")
