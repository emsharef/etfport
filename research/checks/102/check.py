"""Solver checks of claim 102 (M7, one review): the exact criterion, the ETF-optimized test, the
frictionless-spanning closed form, the re-hedge bracket and the budget scaling.

Random assumed instances solved with cvxpy/CLARABEL (floating point, not a certificate). Exits
non-zero on failure. A check, not a proof. Run: uv run python checks/102/check.py
"""
import sys
import numpy as np
import cvxpy as cp

rng = np.random.default_rng(102)
FAIL = []
TOL = 2e-4


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


def solve(mu, Sig, kp, km, xm, xbar, h, fix_funds=None, N=None):
    n = len(mu)
    x = cp.Variable(n)
    u = x - xm
    cost = cp.sum(cp.multiply(kp, cp.pos(u)) + cp.multiply(km, cp.pos(-u)))
    obj = mu @ x - 0.5 * cp.quad_form(x, cp.psd_wrap(Sig)) - cost
    cons = [x >= 0, x <= xbar]
    budget = h - cp.sum(u) - cost >= 0
    cons.append(budget)
    if fix_funds is not None:
        cons.append(x[:N] == fix_funds)
    prob = cp.Problem(cp.Maximize(obj), cons)
    prob.solve(solver=cp.CLARABEL)
    return np.array(x.value).ravel(), float(budget.dual_value), prob.value


def instance(frictionless=False, sigE_zero=False, tight_budget=False):
    N, M, K = 3, 2, 2
    BA = rng.uniform(-0.5, 1.5, (N, K))
    BE = rng.uniform(0.5, 1.5, (M, K)) * np.array([[1.0, 0.2], [0.3, 1.0]])
    Sf = np.diag(rng.uniform(0.002, 0.01, K))
    Pl = np.diag(rng.uniform(0.0, 0.001, K))
    v = rng.uniform(0.0005, 0.004, N)
    SE = np.zeros(M) if (frictionless or sigE_zero) else rng.uniform(0.0, 0.0004, M)
    cE = np.zeros(M) if frictionless else rng.uniform(-0.0005, 0.001, M)
    lam = rng.uniform(0.005, 0.04, K)
    alpha = rng.uniform(-0.01, 0.015, N)
    kpA = rng.uniform(0.0, 0.01, N); kmA = rng.uniform(0.0, 0.01, N)
    kpE = np.zeros(M) if frictionless else rng.uniform(0.0, 0.002, M)
    kmE = np.zeros(M) if frictionless else rng.uniform(0.0, 0.002, M)
    gamma = rng.uniform(2.0, 6.0)
    B = np.vstack([BA, BE])
    Sig = gamma * (B @ (Sf + Pl) @ B.T + np.diag(np.concatenate([v, SE])))
    mu = np.concatenate([alpha + BA @ lam, BE @ lam - cE])
    xm = np.concatenate([rng.uniform(0.0, 0.5, N), rng.uniform(0.2, 2.0, M)])
    xbar = np.full(N + M, 5.0)
    h = 0.02 if tight_budget else 100.0
    return dict(N=N, M=M, K=K, BA=BA, BE=BE, Sf=Sf, Pl=Pl, v=v, SE=SE, cE=cE, lam=lam, alpha=alpha,
                kp=np.concatenate([kpA, kpE]), km=np.concatenate([kmA, kmE]), gamma=gamma, Sig=Sig, mu=mu,
                xm=xm, xbar=xbar, h=h)


def marginal(d, x):
    return d["mu"] - d["Sig"] @ x


def part1(d, x, eta):
    """part 1: residual signs at the optimum."""
    g = marginal(d, x)
    ok = True
    for i in range(len(x)):
        lo, hi = -d["km"][i], d["kp"][i]
        if x[i] > d["xm"][i] + TOL:
            tset = [hi]
        elif x[i] < d["xm"][i] - TOL:
            tset = [lo]
        else:
            tset = None
        if tset is None:
            R_lo = g[i] - eta - (1 + eta) * hi
            R_hi = g[i] - eta - (1 + eta) * lo
        else:
            R_lo = R_hi = g[i] - eta - (1 + eta) * tset[0]
        # some residual R in [R_lo, R_hi] must satisfy the position sign
        if x[i] < TOL:
            ok &= R_lo <= 5 * TOL
        elif x[i] > d["xbar"][i] - TOL:
            ok &= R_hi >= -5 * TOL
        else:
            ok &= (R_lo <= 5 * TOL) and (R_hi >= -5 * TOL)
    return ok


n_cases = {"p1": 0, "p2": 0, "p3": 0, "p4": 0, "p4s": 0, "p4pin": 0, "p5": 0, "p5strip": 0}
for it in range(40):
    d = instance()
    x, eta, val = solve(d["mu"], d["Sig"], d["kp"], d["km"], d["xm"], d["xbar"], d["h"])
    check(eta < 1e-6, "budget unexpectedly binding on a slack instance")
    check(part1(d, x, 0.0), f"part 1 fails on slack instance {it}")
    n_cases["p1"] += 1
    # part 2: ETF-optimized test
    N = d["N"]
    xE, etaE, _ = solve(d["mu"], d["Sig"], d["kp"], d["km"], d["xm"], d["xbar"], d["h"], fix_funds=d["xm"][:N], N=N)
    gE = marginal(d, xE)
    MARG = 3e-5
    held_strict, violated = True, False
    for i in range(N):
        lo, hi = -d["km"][i], d["kp"][i]
        inside = (gE[i] <= hi - MARG) and (xE[i] < TOL or gE[i] >= lo + MARG)
        outside = (gE[i] > hi + MARG) or (xE[i] >= TOL and gE[i] < lo - MARG)
        held_strict &= inside
        violated |= outside
    no_trade = np.all(np.abs(x[:N] - d["xm"][:N]) < 5 * TOL)
    if held_strict:
        check(no_trade, f"part 2: all funds held at x_E but the solver trades a fund, instance {it}")
    elif violated:
        check(not no_trade, f"part 2: a fund's held condition fails at x_E but the solver trades no fund, instance {it}")
    n_cases["p2"] += 1

for it in range(120):
    d = instance(frictionless=True)
    x, eta, _ = solve(d["mu"], d["Sig"], d["kp"], d["km"], d["xm"], d["xbar"], d["h"])
    N, M = d["N"], d["M"]
    if np.any(x[N:] < TOL) or np.any(x > d["xbar"] - TOL):
        continue   # an ETF bound binds: outside part 3's hypothesis
    g = d["gamma"]
    Sft = d["Sf"] + d["Pl"]
    ystar = np.linalg.solve(g * Sft, d["lam"])
    lo = (d["alpha"] - d["kp"][:N]) / (g * d["v"])
    hi = (d["alpha"] + d["km"][:N]) / (g * d["v"])
    xA = np.clip(np.clip(d["xm"][:N], lo, hi), 0.0, d["xbar"][:N])
    R = np.linalg.inv(d["BE"])
    xE = R.T @ (ystar - d["BA"].T @ xA)
    check(np.max(np.abs(x[:N] - xA)) < 5 * TOL and np.max(np.abs(x[N:] - xE)) < 5 * TOL,
          f"part 3 closed form differs from the solver on instance {it}")
    n_cases["p3"] += 1

for it in range(120):
    sz = it % 2 == 0
    d = instance(sigE_zero=sz)
    x, eta, _ = solve(d["mu"], d["Sig"], d["kp"], d["km"], d["xm"], d["xbar"], d["h"])
    N, M = d["N"], d["M"]
    if np.any(x[N:] < TOL) or np.any(x[N:] > d["xbar"][N:] - TOL):
        continue
    R = np.linalg.inv(d["BE"])
    g = d["gamma"]
    for i in range(N):
        r = R.T @ d["BA"][i]
        hp = np.sum(np.maximum(r, 0) * d["km"][N:] + np.maximum(-r, 0) * d["kp"][N:])   # netting a purchase sells the r>0 ETFs
        hm = np.sum(np.maximum(r, 0) * d["kp"][N:] + np.maximum(-r, 0) * d["km"][N:])   # netting a sale buys them
        def A(xx):
            return d["alpha"][i] + r @ d["cE"] - g * d["v"][i] * xx[i] + g * (r * d["SE"]) @ xx[N:]
        Ai = A(x)
        if x[i] > d["xm"][i] + TOL:
            check(Ai >= d["kp"][i] - hm - 5 * TOL, f"part 4 bought bracket fails, instance {it} fund {i}")
        elif x[i] < d["xm"][i] - TOL:
            check(Ai <= -d["km"][i] + hp + 5 * TOL, f"part 4 sold bracket fails, instance {it} fund {i}")
        elif TOL < x[i] < d["xbar"][i] - TOL:
            check(-d["km"][i] - hm - 5 * TOL <= Ai <= d["kp"][i] + hp + 5 * TOL, f"part 4 held bracket fails, instance {it} fund {i}")
        n_cases["p4"] += 1
        # pinned slopes: every ETF traded gives the exact threshold A_i = +-kappa_i - r' t
        bought_E = x[N:] > d["xm"][N:] + TOL; sold_E = x[N:] < d["xm"][N:] - TOL
        if np.all(bought_E | sold_E):
            t = np.where(bought_E, d["kp"][N:], -d["km"][N:])
            if x[i] > d["xm"][i] + TOL and x[i] < d["xbar"][i] - TOL:
                check(abs(Ai - (d["kp"][i] - r @ t)) < 5 * TOL, f"part 4 pinned-slope purchase threshold fails, instance {it} fund {i}")
                n_cases["p4pin"] += 1
            elif x[i] < d["xm"][i] - TOL and x[i] > TOL:
                check(abs(Ai - (-d["km"][i] - r @ t)) < 5 * TOL, f"part 4 pinned-slope sale threshold fails, instance {it} fund {i}")
                n_cases["p4pin"] += 1
        if sz:
            A0 = A(d["xm"])
            if A0 > d["kp"][i] + hp + 5 * TOL:
                check(x[i] > d["xm"][i] + TOL, f"part 4 sufficient purchase condition fails, instance {it} fund {i}")
                n_cases["p4s"] += 1
            if A0 < -d["km"][i] - hm - 5 * TOL:
                check(x[i] < d["xm"][i] - TOL, f"part 4 sufficient sale condition fails, instance {it} fund {i}")
                n_cases["p4s"] += 1

for it in range(80):
    d = instance(tight_budget=True)
    x, eta, _ = solve(d["mu"], d["Sig"], d["kp"], d["km"], d["xm"], d["xbar"], d["h"])
    if eta < 1e-5:
        continue
    check(part1(d, x, eta), f"part 5(a) scaling fails with eta={eta:.4f} on instance {it}")
    n_cases["p5"] += 1

# part 5(a) on part 3's strip: frictionless spanning ETFs with a binding budget; the thresholds on
# alpha_hat_i - gamma v_i x^-_i shift by eta (1 - sum_j r_ij), the clip and the exposure target follow
for it in range(120):
    d = instance(frictionless=True, tight_budget=True)
    x, eta, _ = solve(d["mu"], d["Sig"], d["kp"], d["km"], d["xm"], d["xbar"], d["h"])
    N, M = d["N"], d["M"]
    if eta < 1e-5 or np.any(x[N:] < TOL) or np.any(x > d["xbar"] - TOL):
        continue
    g = d["gamma"]; R = np.linalg.inv(d["BE"])
    shift = eta * (1.0 - (d["BA"] @ R).sum(axis=1))          # eta (1 - sum_j r_ij), r_i' = B^A_i R
    lo = (d["alpha"] - shift - (1 + eta) * d["kp"][:N]) / (g * d["v"])
    hi = (d["alpha"] - shift + (1 + eta) * d["km"][:N]) / (g * d["v"])
    xA = np.clip(np.clip(d["xm"][:N], lo, hi), 0.0, d["xbar"][:N])
    check(np.max(np.abs(x[:N] - xA)) < 5 * TOL, f"part 5(a) shifted clip differs from the solver, instance {it}")
    strip = d["alpha"] - g * d["v"] * d["xm"][:N]
    for i in range(N):
        if x[i] > d["xm"][i] + TOL:
            check(strip[i] > shift[i] + (1 + eta) * d["kp"][i] - 5 * TOL, f"part 5(a) purchase threshold fails, instance {it} fund {i}")
        elif x[i] < d["xm"][i] - TOL:
            check(strip[i] < shift[i] - (1 + eta) * d["km"][i] + 5 * TOL, f"part 5(a) sale threshold fails, instance {it} fund {i}")
    ystar = np.linalg.solve(g * (d["Sf"] + d["Pl"]), d["lam"] - eta * R @ np.ones(M))
    check(np.max(np.abs(d["BE"].T @ x[N:] + d["BA"].T @ x[:N] - ystar)) < 5 * TOL, f"part 5(a) exposure target y*(eta) differs from the solver, instance {it}")
    n_cases["p5strip"] += 1

print("cases:", n_cases)
check(n_cases["p3"] >= 10 and n_cases["p4s"] >= 5 and n_cases["p4pin"] >= 5 and n_cases["p5"] >= 3 and n_cases["p5strip"] >= 3, "too few instances exercised a part")
if FAIL:
    print(f"{len(FAIL)} check(s) failed")
    sys.exit(1)
print("all checks passed")
