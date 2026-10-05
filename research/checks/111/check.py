"""Solver checks of claim 111 (M7, one review): the incumbent-aware first stage (the ETF-only problem
with ETF costs, fees, the zero bound and the budget), when the resulting two-stage procedure is
exact, and its loss in the inputs through the ETF-line residual.

Random assumed instances solved with cvxpy/CLARABEL (floating point, not a certificate). Exits
non-zero on failure. A check, not a proof. Run: uv run python checks/111/check.py

 (i)   part 2: the fibre problem's multiplier for the exposure is a supergradient of the fibre value
       V at w_1 (tested against V at the joint exposure), the loss lies in [0, min(s'(w_J - w_1),
       s' Sigma_EE^{-1} s/(2 gamma))], and the exposure gap is at most |s|_{Sigma_EE^{-1}}/gamma;
 (ii)  part 2: exact iff the residual vanishes (both directions, at solver tolerance); for traded
       interior ETFs the residual is g_j(x_2) - eta_2 - (1 + eta_2) t_j;
 (iii) part 3: the hold test at the ETF-only optimum gives exactness; every ETF traded at stage 1 in
       directions stage 2 keeps, with a slack budget, gives exactness;
 (iv)  the same bounds for claim 041's frictionless one-sided first stage (part 4).
"""
import sys
import numpy as np
import cvxpy as cp

rng = np.random.default_rng(111)
FAIL = []
TOL = 2e-4
MTOL = 3e-5


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


def instance(N=3, M=2, tight=False, costE=True):
    K = M
    BA = rng.uniform(-0.5, 1.5, (N, K))
    BE = rng.uniform(0.6, 1.4, (M, K)) * (np.eye(K) + 0.25 * rng.uniform(0, 1, (K, K)))
    Sf = np.diag(rng.uniform(0.002, 0.01, K)) + np.diag(rng.uniform(0.0, 0.001, K))
    v = rng.uniform(0.0005, 0.004, N)
    cE = rng.uniform(-0.0005, 0.0015, M)
    lam = rng.uniform(-0.01, 0.03, K)
    alpha = rng.uniform(-0.01, 0.015, N)
    kpA = rng.uniform(0.0, 0.01, N); kmA = rng.uniform(0.0, 0.01, N)
    kpE = rng.uniform(0.0, 0.002, M); kmE = rng.uniform(0.0, 0.002, M)
    if not costE:
        kpE[:] = 0.0; kmE[:] = 0.0
    gamma = rng.uniform(2.0, 6.0)
    B = np.vstack([BA, BE])
    gSig = gamma * (B @ Sf @ B.T + np.diag(np.concatenate([v, np.zeros(M)])))
    mu = np.concatenate([alpha + BA @ lam, BE @ lam - cE])
    xmE = rng.uniform(0.0, 1.5, M)
    if rng.uniform() < 0.5:
        xmE[rng.integers(M)] = 0.0
    xm = np.concatenate([rng.uniform(0.0, 0.5, N), xmE])
    xbar = np.concatenate([np.full(N, 5.0), np.full(M, 1e6)])
    h = rng.uniform(0.0, 0.03) if tight else 100.0
    R = np.linalg.inv(BE); Q = R.T @ BA.T
    return dict(N=N, M=M, gamma=gamma, gSig=gSig, mu=mu, kp=np.concatenate([kpA, kpE]), km=np.concatenate([kmA, kmE]),
                xm=xm, xbar=xbar, h=h, Q=Q, SEE=BE @ Sf @ BE.T, muE=BE @ lam - cE, v=v, alpha=alpha, cE=cE, at=alpha + Q.T @ cE)


def solve(d, fix_A=None, fibre_w=None):
    n = d["N"] + d["M"]; N = d["N"]
    x = cp.Variable(n); u = x - d["xm"]
    cost = cp.sum(cp.multiply(d["kp"], cp.pos(u)) + cp.multiply(d["km"], cp.pos(-u)))
    obj = d["mu"] @ x - 0.5 * cp.quad_form(x, cp.psd_wrap(d["gSig"])) - cost
    cons = [x >= 0, x <= d["xbar"]]
    budget = d["h"] - cp.sum(u) - cost >= 0
    cons.append(budget)
    fib = None
    if fix_A is not None:
        cons.append(x[:N] == fix_A)
    if fibre_w is not None:
        fib = x[N:] + d["Q"] @ x[:N] == fibre_w
        cons.append(fib)
    p = cp.Problem(cp.Maximize(obj), cons)
    try:
        p.solve(solver=cp.CLARABEL)
    except Exception:
        return None
    if x.value is None:
        return None
    xv = np.array(x.value).ravel()
    s = None if fib is None else -np.array(fib.dual_value).ravel()      # dV/dw: sign convention of the equality's dual
    return dict(x=xv, eta=float(budget.dual_value), val=float(p.value), s=s)


def jointvalue(d, x):
    u = x - d["xm"]
    return d["mu"] @ x - 0.5 * x @ d["gSig"] @ x - np.sum(d["kp"] * np.maximum(u, 0) + d["km"] * np.maximum(-u, 0))


def marginal(d, x):
    return d["mu"] - d["gSig"] @ x


def stage1_frictionless(d):
    N, M = d["N"], d["M"]
    w = cp.Variable(M); xA = cp.Variable(N)
    obj = d["muE"] @ w - 0.5 * d["gamma"] * cp.quad_form(w, cp.psd_wrap(d["SEE"]))
    p = cp.Problem(cp.Maximize(obj), [w >= d["Q"] @ xA, xA >= 0, xA <= d["xbar"][:N]]); p.solve(solver=cp.CLARABEL)
    return np.array(w.value).ravel()


SIGN = [None]          # the solver's sign convention for the equality's dual, fixed once by the supergradient test below


def fix_sign(d, w1, r2):
    """Fix the dual's sign so that s is a supergradient of V at w1: V(w1 +- delta e_j) <= V(w1) +- s_j delta."""
    M = d["M"]; s = r2["s"]; j = int(np.argmax(np.abs(s)))
    if abs(s[j]) < 1e-3:
        return
    delta = 1e-3 * (1 + abs(w1[j]))
    e = np.zeros(M); e[j] = delta
    rp, rm = solve(d, fibre_w=w1 + e), solve(d, fibre_w=w1 - e)
    if rp is None or rm is None:
        return
    for sign in (1.0, -1.0):
        ok = (rp["val"] <= r2["val"] + sign * s[j] * delta + 1e-9) and (rm["val"] <= r2["val"] - sign * s[j] * delta + 1e-9)
        if ok:
            SIGN[0] = sign; return


def run_procedure(d, w1, xJ, J, tag, it, counts):
    """stage 2 on the fibre of w1; the residual s from the fibre's exposure multiplier; the bounds."""
    N, M = d["N"], d["M"]
    r2 = solve(d, fibre_w=w1)
    if r2 is None:
        counts[tag + "_inf"] += 1; return None
    if SIGN[0] is None:
        fix_sign(d, w1, r2)
        if SIGN[0] is None:
            return None
    x2, s = r2["x"], SIGN[0] * r2["s"]
    wJ = xJ[N:] + d["Q"] @ xJ[:N]
    T = jointvalue(d, x2); Lam = J - T
    SEEi = np.linalg.inv(d["SEE"])
    bound1 = float(s @ (wJ - w1)); bound2 = float(s @ SEEi @ s) / (2 * d["gamma"])
    exact = np.max(np.abs(x2 - xJ)) < 5 * TOL
    dxA = xJ[:N] - x2[:N]; dwv = wJ - w1
    lower = 0.5 * d["gamma"] * (dxA @ np.diag(d["v"]) @ dxA + dwv @ d["SEE"] @ dwv)
    check(Lam >= lower - 1e-7, f"{tag}: loss {Lam:.3e} below the misplacement lower bound {lower:.3e} on instance {it}")
    check(Lam <= min(bound1, bound2) + 1e-7, f"{tag}: loss {Lam:.3e} exceeds min({bound1:.3e}, {bound2:.3e}) on instance {it}")
    dw = wJ - w1
    check(np.sqrt(dw @ d["SEE"] @ dw) <= np.sqrt(s @ SEEi @ s) / d["gamma"] + 1e-6, f"{tag}: exposure gap bound fails on instance {it}")
    # a zero residual gives exactness; exactness forces a zero residual where the fibre's multiplier is pinned
    # (ETFs traded and interior at x_2); at an ETF at zero or untraded the supergradient is not unique
    # (with a binding budget the fibre problem's cash multiplier need not be the joint's, and the pair (eta_2, s) is
    # not unique, so the pinned test is made only when the budget is slack on the fibre)
    pinned = [j for j in range(M) if x2[N + j] > TOL and abs(x2[N + j] - d["xm"][N + j]) > TOL]
    if exact and r2["eta"] < 1e-6:
        check(all(abs(s[j]) < 10 * MTOL for j in pinned), f"{tag}: exact but a pinned residual is nonzero on instance {it}")
    else:
        check(np.max(np.abs(s)) > MTOL / 10, f"{tag}: inexact with a zero residual on instance {it}")
    # residual form for traded interior ETFs: g_j(x_2) - eta_2 - (1 + eta_2) t_j
    g2 = marginal(d, x2); eta2 = r2["eta"]
    for j in range(M):
        xj, xmj = x2[N + j], d["xm"][N + j]
        if xj > TOL and abs(xj - xmj) > TOL:
            t = d["kp"][N + j] if xj > xmj else -d["km"][N + j]
            check(abs(s[j] - (g2[N + j] - eta2 - (1 + eta2) * t)) < 10 * MTOL, f"{tag}: residual form fails on instance {it} ETF {j}: {s[j]:.2e} vs {g2[N + j] - eta2 - (1 + eta2) * t:.2e}")
    counts[tag] += 1; counts[tag + "_x"] += int(exact)
    return dict(x2=x2, s=s, Lam=Lam, exact=exact, eta2=eta2)


counts = dict(inc=0, inc_x=0, inc_inf=0, fr=0, fr_x=0, fr_inf=0, hold=0, alltraded=0, costly_x=0)
for it in range(240):
    costE = (it % 4 != 3)
    d = instance(tight=(it % 2 == 0), costE=costE)
    rJ = solve(d)
    if rJ is None:
        continue
    xJ, J = rJ["x"], rJ["val"]
    N, M = d["N"], d["M"]
    # incumbent-aware first stage: the ETF-only problem from the incumbents
    r1 = solve(d, fix_A=d["xm"][:N])
    x1 = r1["x"]; w1 = x1[N:] + d["Q"] @ d["xm"][:N]
    out = run_procedure(d, w1, xJ, J, "inc", it, counts)
    if out is not None:
        # part 3(a): hold test at the ETF-only optimum (claim 102 part 2) => exact
        g1 = marginal(d, x1); eta1 = r1["eta"]; held = True
        for i in range(N):
            lo, hi = eta1 - (1 + eta1) * d["km"][i], eta1 + (1 + eta1) * d["kp"][i]
            inside = (g1[i] <= hi - MTOL) and (x1[i] < TOL or g1[i] >= lo + MTOL)
            held &= inside
        if held:
            check(out["exact"], f"part 3(a): every fund held at the ETF-only optimum but the procedure is inexact on instance {it}")
            counts["hold"] += 1
        # part 3(c): every ETF traded at stage 1, directions kept at x_2, budget slack in both => exact
        d1 = np.sign(np.where(np.abs(x1[N:] - d["xm"][N:]) > TOL, x1[N:] - d["xm"][N:], 0.0))
        d2 = np.sign(np.where(np.abs(out["x2"][N:] - d["xm"][N:]) > TOL, out["x2"][N:] - d["xm"][N:], 0.0))
        if np.all(d1 != 0) and np.all(x1[N:] > TOL) and np.all(out["x2"][N:] > TOL) and np.array_equal(d1, d2) and eta1 < 1e-6 and out["eta2"] < 1e-6:
            check(out["exact"], f"part 3(c): all ETFs traded with kept directions and slack budget but inexact on instance {it}")
            counts["alltraded"] += 1
        counts["costly_x"] += int(out["exact"] and costE)
    # claim 041's frictionless one-sided first stage, same bounds (part 4)
    wst = stage1_frictionless(d)
    run_procedure(d, wst, xJ, J, "fr", it, counts)

print("cases:", counts)
check(counts["inc"] >= 100 and counts["inc_x"] >= 10 and counts["hold"] >= 3 and counts["alltraded"] >= 3 and counts["fr"] >= 100, "too few instances exercised a part")
if FAIL:
    print(f"{len(FAIL)} check(s) failed"); sys.exit(1)
print("all checks passed")
