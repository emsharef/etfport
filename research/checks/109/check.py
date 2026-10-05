"""Solver checks of claim 109 (M7, one review): the fund decision and two-stage exactness with some
ETFs at zero, the others costly, fees on and a possibly binding budget.

Random assumed instances solved with cvxpy/CLARABEL (floating point, not a certificate). Exits
non-zero on failure. A check, not a proof. Run: uv run python checks/109/check.py

 (i)   part 1: the joint criterion at the optimum (fund and ETF lines with the cash multiplier from
       the solver's dual, the at-zero slacks and the trade-sign slopes), with ETF residual risk on;
 (ii)  part 2 (Sigma_E = 0): given the ETF status partition read off the optimum (traded, idle, at zero),
       the traded ETFs' holdings, every fund's marginal alpha^{F,T}_i - gamma (V^{F,T} x^A)_i with the
       effective netting weights, the at-zero slacks, and the at-zero test, all in the inputs;
 (iii) part 3 (one fund, one ETF): the status thresholds and the fund rule in each status;
 (iv)  part 4: the fibre-confined procedure (one-sided stage 1, stage 2 with all frictions and the
       budget) is exact iff stage 2's holdings satisfy the joint criterion with stage 1's slacks; with
       costly ETFs it is exact only when stage 2 trades no interior ETF (up to coincidences); the soft
       procedure with an unconstrained stage 1 is exact with everything on, and with the one-sided
       stage 1 its loss is bounded by the slack-tilt times the exposure gap.
"""
import sys
import numpy as np
import cvxpy as cp

rng = np.random.default_rng(109)
FAIL = []
TOL = 2e-4          # holdings
MTOL = 3e-5         # marginals (solver gaps are 1e-8; ETF rates are 1e-3 or less)


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


def instance(N=3, M=2, sigE=True, tight=False, fees=True, one=False, costE=True):
    K = M
    if one:
        N = 1; M = K = 1
    BA = rng.uniform(-0.5, 1.5, (N, K))
    BE = rng.uniform(0.6, 1.4, (M, K)) * (np.eye(K) + 0.25 * rng.uniform(0, 1, (K, K)))
    Sf = np.diag(rng.uniform(0.002, 0.01, K)) + np.diag(rng.uniform(0.0, 0.001, K))
    v = rng.uniform(0.0005, 0.004, N)
    SE = rng.uniform(0.0, 0.0004, M) if sigE else np.zeros(M)
    cE = rng.uniform(-0.0005, 0.0015, M) if fees else np.zeros(M)
    lam = rng.uniform(-0.01, 0.03, K)                      # some premia small or negative: ETFs at zero
    alpha = rng.uniform(-0.01, 0.015, N)
    kpA = rng.uniform(0.0, 0.01, N); kmA = rng.uniform(0.0, 0.01, N)
    kpE = rng.uniform(0.0, 0.002, M); kmE = rng.uniform(0.0, 0.002, M)
    if not costE:
        kpE[:] = 0.0; kmE[:] = 0.0
    gamma = rng.uniform(2.0, 6.0)
    B = np.vstack([BA, BE])
    Sig = gamma * (B @ Sf @ B.T + np.diag(np.concatenate([v, SE])))     # gamma Sigma
    mu = np.concatenate([alpha + BA @ lam, BE @ lam - cE])
    xmE = rng.uniform(0.0, 1.5, M); xmE[rng.integers(M)] = 0.0          # at least one ETF starts at zero
    xm = np.concatenate([rng.uniform(0.0, 0.5, N), xmE])
    xbar = np.concatenate([np.full(N, 5.0), np.full(M, 1e6)])           # ETF caps absent
    h = rng.uniform(0.0, 0.03) if tight else 100.0
    R = np.linalg.inv(BE); Q = R.T @ BA.T                                 # columns r_i
    return dict(N=N, M=M, K=K, BA=BA, BE=BE, Sf=Sf, v=v, SE=SE, cE=cE, lam=lam, alpha=alpha,
                kp=np.concatenate([kpA, kpE]), km=np.concatenate([kmA, kmE]), gamma=gamma, gSig=Sig, mu=mu,
                xm=xm, xbar=xbar, h=h, R=R, Q=Q, SEE=BE @ Sf @ BE.T, muE=BE @ lam - cE, at=alpha + Q.T @ cE)


def solve(d, fix_A=None, fibre_w=None, tilt=None, track=None):
    """Joint problem (default). fix_A: fund holdings fixed. fibre_w: x^E = w - Q x^A (fibre-confined stage 2).
    track: (w_s) soft stage 2, G_E replaced by -(gamma/2)(w - w_s)' SEE (w - w_s)."""
    n = d["N"] + d["M"]; N = d["N"]
    x = cp.Variable(n); u = x - d["xm"]
    cost = cp.sum(cp.multiply(d["kp"], cp.pos(u)) + cp.multiply(d["km"], cp.pos(-u)))
    if track is None:
        obj = d["mu"] @ x - 0.5 * cp.quad_form(x, cp.psd_wrap(d["gSig"])) - cost
    else:
        w = x[N:] + d["Q"] @ x[:N]
        obj = (d["at"] @ x[:N] - 0.5 * d["gamma"] * cp.quad_form(x[:N], cp.psd_wrap(np.diag(d["v"])))
               - 0.5 * d["gamma"] * cp.quad_form(w - track, cp.psd_wrap(d["SEE"]))
               - 0.5 * cp.quad_form(x[N:], cp.psd_wrap(d["gamma"] * np.diag(d["SE"]))) - cost)
    cons = [x >= 0, x <= d["xbar"]]
    budget = d["h"] - cp.sum(u) - cost >= 0
    cons.append(budget)
    if fix_A is not None:
        cons.append(x[:N] == fix_A)
    if fibre_w is not None:
        cons.append(x[N:] == fibre_w - d["Q"] @ x[:N])
    p = cp.Problem(cp.Maximize(obj), cons)
    try:
        p.solve(solver=cp.CLARABEL)
    except Exception:
        return None, None, None
    if x.value is None:
        return None, None, None            # infeasible (a fibre the budget cannot fund)
    xv = np.array(x.value).ravel()
    return xv, float(budget.dual_value), p.value


def jointvalue(d, x):
    u = x - d["xm"]
    return d["mu"] @ x - 0.5 * x @ d["gSig"] @ x - np.sum(d["kp"] * np.maximum(u, 0) + d["km"] * np.maximum(-u, 0))


def marginal(d, x):
    return d["mu"] - d["gSig"] @ x


def statuses(d, x):
    """ETF statuses at x: Z (at zero), B (bought), S (sold, interior), I (idle interior)."""
    N, M = d["N"], d["M"]; xE = x[N:]; xmE = d["xm"][N:]
    Z = [j for j in range(M) if xE[j] < TOL]
    Bt = [j for j in range(M) if j not in Z and xE[j] > xmE[j] + TOL]
    S = [j for j in range(M) if j not in Z and xE[j] < xmE[j] - TOL]
    I = [j for j in range(M) if j not in Z and j not in Bt and j not in S]
    return Z, Bt, S, I


def slope_sets(d, x):
    """T_i(x) as (lo, hi) per instrument."""
    n = len(x); out = []
    for i in range(n):
        if x[i] > d["xm"][i] + TOL:
            out.append((d["kp"][i], d["kp"][i]))
        elif x[i] < d["xm"][i] - TOL:
            out.append((-d["km"][i], -d["km"][i]))
        else:
            out.append((-d["km"][i], d["kp"][i]))
    return out


def part1_ok(d, x, eta, ret_zeta=False):
    """Every instrument's line: g_i - eta - (1 + eta) t_i = R_i with the box sign, for some t_i in T_i."""
    g = marginal(d, x); ts = slope_sets(d, x); ok = True; zeta = np.zeros(len(x))
    for i in range(len(x)):
        lo, hi = ts[i]
        Rlo = g[i] - eta - (1 + eta) * hi; Rhi = g[i] - eta - (1 + eta) * lo
        if x[i] < TOL:
            ok &= Rlo <= MTOL; zeta[i] = max(0.0, -Rlo)
        elif x[i] > d["xbar"][i] - TOL:
            ok &= Rhi >= -MTOL
        else:
            ok &= (Rlo <= MTOL) and (Rhi >= -MTOL)
    return (ok, zeta) if ret_zeta else ok


counts = dict(p1=0, p1z=0, p2=0, p2T=0, p2z=0, p3=0, p4=0, p4x=0, p4t=0, p4s=0, p4b=0, p4inf=0, p4xc=0, p4xb=0)

# (i) part 1 with ETF residual risk, fees, costs, a tight budget
for it in range(120):
    d = instance(sigE=True, tight=(it % 2 == 0))
    x, eta, J = solve(d)
    Z, Bt, S, I = statuses(d, x)
    ok, zeta = part1_ok(d, x, eta, ret_zeta=True)
    check(ok, f"part 1 fails on instance {it} (eta {eta:.4f}, Z {Z})")
    # the fund line written with the slacks: A_i + r_i'(eta 1 + (1+eta) t_E) - sum_Z r_ij zeta_j = eta + (1+eta) t_i
    N, M = d["N"], d["M"]; g = marginal(d, x); ts = slope_sets(d, x)
    for i in range(N):
        r = d["Q"][:, i]
        A = d["alpha"][i] + r @ d["cE"] - d["gamma"] * d["v"][i] * x[i] + d["gamma"] * (r * d["SE"]) @ x[N:]
        # t_E: for traded ETFs pinned; for idle ETFs t_j = (g_j - eta)/(1+eta); for Z: t_j the convention, zeta the slack
        tE = np.zeros(M)
        for j in range(M):
            if j in Z:
                tE[j] = d["kp"][N + j] if d["xm"][N + j] < TOL else -d["km"][N + j]
            elif j in Bt:
                tE[j] = d["kp"][N + j]
            elif j in S:
                tE[j] = -d["km"][N + j]
            else:
                tE[j] = (g[N + j] - eta) / (1 + eta)
        lhs = A + r @ (eta + (1 + eta) * tE) - sum(r[j] * zeta[N + j] for j in Z)
        check(abs(lhs - g[i]) < MTOL, f"part 1 fund-line identity fails on instance {it} fund {i}")
    counts["p1"] += 1; counts["p1z"] += int(len(Z) > 0)

# (ii) part 2: Sigma_E = 0, explicit forms given the status partition
for it in range(160):
    d = instance(sigE=False, tight=(it % 2 == 0))
    x, eta, J = solve(d)
    if not part1_ok(d, x, eta):
        continue
    Z, Bt, S, I = statuses(d, x)
    N, M = d["N"], d["M"]; g = marginal(d, x); SEE = d["SEE"]; muE = d["muE"]; Q = d["Q"]; gam = d["gamma"]
    T = sorted(Bt + S); F = sorted(Z + I)
    tT = np.array([d["kp"][N + j] if j in Bt else -d["km"][N + j] for j in T])
    piT = eta + (1 + eta) * tT
    xF = x[N:][F]; q = Q @ x[:N]
    if T:
        STTi = np.linalg.inv(SEE[np.ix_(T, T)])
        xT = STTi @ ((muE[T] - piT) / gam - (SEE[T] @ q) - SEE[np.ix_(T, F)] @ xF)
        check(np.max(np.abs(xT - x[N:][T])) < 5 * TOL, f"part 2a traded holdings differ on instance {it}")
        muFT = muE[F] - SEE[np.ix_(F, T)] @ STTi @ muE[T]
        SFFT = SEE[np.ix_(F, F)] - SEE[np.ix_(F, T)] @ STTi @ SEE[np.ix_(T, F)]
        hedge = SEE[np.ix_(F, T)] @ STTi @ piT
        counts["p2T"] += 1
    else:
        muFT = muE[F].copy(); SFFT = SEE[np.ix_(F, F)]; hedge = np.zeros(len(F)); STTi = None
    wF = q[F] + xF
    # at-zero slacks and the fixed ETFs' marginals in the inputs
    gF = muFT + hedge - gam * SFFT @ wF
    check(np.max(np.abs(gF - g[N:][F])) < MTOL if F else True, f"part 2c fixed-ETF marginals differ on instance {it}")
    for j in Z:
        thr = eta + (1 + eta) * (d["kp"][N + j] if d["xm"][N + j] < TOL else -d["km"][N + j])
        check(g[N + j] <= thr + MTOL, f"part 2d at-zero test fails on instance {it} ETF {j}")
        counts["p2z"] += 1
    for j in range(M):
        if d["xm"][N + j] < TOL and j not in Z:
            check(abs(g[N + j] - (eta + (1 + eta) * d["kp"][N + j])) < MTOL, f"part 2d bought-from-zero line fails on instance {it} ETF {j}")
    # fund marginals with the effective netting weights
    VFT = np.diag(d["v"]) + (Q[F].T @ SFFT @ Q[F] if F else 0.0)
    for i in range(N):
        r = Q[:, i]; rF = r[F]; rT = r[T]
        rho = rT + (STTi @ SEE[np.ix_(T, F)] @ rF if T else 0.0)
        aFT = d["at"][i] + (rF @ muFT if F else 0.0) - (gam * rF @ SFFT @ xF if F else 0.0) + (rho @ piT if T else 0.0)
        Gi = aFT - gam * (VFT @ x[:N])[i]
        check(abs(Gi - g[i]) < MTOL, f"part 2b fund marginal differs on instance {it} fund {i} (T {T}, F {F})")
        # the netted cash shift over traded ETFs and the scaled slopes: G_i = eta + (1+eta) t_i within the box
        lo, hi = slope_sets(d, x)[i]
        if TOL < x[i] < d["xbar"][i] - TOL:
            check(eta + (1 + eta) * lo - MTOL <= Gi <= eta + (1 + eta) * hi + MTOL, f"part 2b fund condition fails on instance {it} fund {i}")
    counts["p2"] += 1

# (iii) part 3: one fund, one ETF, Sigma_E = 0
for it in range(120):
    d = instance(sigE=False, tight=(it % 3 == 0), one=True)
    x, eta, J = solve(d)
    if not part1_ok(d, x, eta):
        continue
    N = 1; g = marginal(d, x); r = float(d["Q"][0, 0]); sEE = float(d["SEE"][0, 0]); muE = float(d["muE"][0]); gam = d["gamma"]
    kpE, kmE = d["kp"][1], d["km"][1]; a, p = x[0], x[1]; pm = d["xm"][1]
    Z, Bt, S, I = statuses(d, x)
    gE = muE - gam * sEE * (r * a + p)
    if Z:      # at zero: marginal at most the (scaled) purchase threshold; fund marginal is the fund-alone form
        thr = eta + (1 + eta) * (kpE if pm < TOL else -kmE)
        check(gE <= thr + MTOL, f"part 3 at-zero threshold fails on instance {it}")
        Gi = d["at"][0] + r * muE - gam * (d["v"][0] + r * r * sEE) * a
    elif I:    # idle: the fund-alone form with the ETF's holding
        Gi = d["at"][0] + r * muE - gam * (d["v"][0] + r * r * sEE) * a - gam * r * sEE * p
    else:      # traded: the pinned-slope form
        t = kpE if Bt else -kmE
        Gi = d["at"][0] + r * (eta + (1 + eta) * t) - gam * d["v"][0] * a
    check(abs(Gi - g[0]) < MTOL, f"part 3 fund marginal form fails on instance {it} (Z {Z} B {Bt} S {S} I {I})")
    counts["p3"] += 1

# (iv) part 4: the two procedures, Sigma_E = 0
def stage1(d):
    N, M = d["N"], d["M"]
    w = cp.Variable(M); xA = cp.Variable(N)
    obj = d["muE"] @ w - 0.5 * d["gamma"] * cp.quad_form(w, cp.psd_wrap(d["SEE"]))
    p = cp.Problem(cp.Maximize(obj), [w >= d["Q"] @ xA, xA >= 0, xA <= d["xbar"][:N]]); p.solve(solver=cp.CLARABEL)
    wst = np.array(w.value).ravel()
    return wst, d["gamma"] * d["SEE"] @ wst - d["muE"]


for it in range(240):
    costE = (it % 3 != 2)                                   # a third of the instances have frictionless ETFs (claim 041's case, fees on)
    d = instance(sigE=False, tight=(it % 2 == 0), costE=costE)
    xJ, etaJ, J = solve(d)
    if not part1_ok(d, xJ, etaJ):
        continue
    N, M = d["N"], d["M"]
    wst, zst = stage1(d)
    check(np.min(zst) > -MTOL, f"part 4: stage 1 slacks negative on instance {it}")
    # fibre-confined stage 2: x^E = w* - Q x^A >= 0, all frictions and the budget
    x2, eta2, T2 = solve(d, fibre_w=wst)
    if x2 is None:
        counts["p4inf"] += 1; continue     # stage 1's fibre is not fundable: the procedure fails outright
    exact = np.max(np.abs(x2 - xJ)) < 5 * TOL          # the joint optimum is unique
    # criterion at x_2 with stage 1's slacks: fund lines alpha~ - gamma V x_2 - r' zeta* = eta + (1+eta) t_i (box signs),
    # and ETF lines: interior ETFs -zeta*_j = eta + (1+eta) t_j; at zero one-sided. Test with the fibre problem's eta.
    def criterion(eta):
        ts = slope_sets(d, x2); ok = True
        for i in range(N):
            r = d["Q"][:, i]
            Gi = d["at"][i] - d["gamma"] * d["v"][i] * x2[i] - r @ zst
            lo, hi = ts[i]
            if x2[i] < TOL:
                ok &= Gi <= eta + (1 + eta) * hi + MTOL
            elif x2[i] > d["xbar"][i] - TOL:
                ok &= Gi >= eta + (1 + eta) * lo - MTOL
            else:
                ok &= eta + (1 + eta) * lo - MTOL <= Gi <= eta + (1 + eta) * hi + MTOL
        for j in range(M):
            lo, hi = ts[N + j]
            if x2[N + j] < TOL:
                ok &= -zst[j] <= eta + (1 + eta) * hi + MTOL
            else:
                ok &= eta + (1 + eta) * lo - MTOL <= -zst[j] <= eta + (1 + eta) * hi + MTOL
        return ok
    if exact:
        check(criterion(etaJ), f"part 4: exact but the criterion fails at x_2 with the joint eta on instance {it}")
        # exact with a traded interior ETF only at a coincidence
        Z2, B2, S2, I2 = statuses(d, x2)
        for j in B2 + S2:
            t = d["kp"][N + j] if j in B2 else -d["km"][N + j]
            check(abs(-zst[j] - (etaJ + (1 + etaJ) * t)) < MTOL, f"part 4: exact with a traded interior ETF off the coincidence line on instance {it}")
        counts["p4x"] += 1
        counts["p4t"] += int(len(B2 + S2) > 0)
        counts["p4xc"] += int(costE); counts["p4xb"] += int(etaJ > 1e-5)
    else:
        check(not criterion(eta2), f"part 4: criterion holds at x_2 (fibre eta) but the procedure is inexact on instance {it}")
    counts["p4"] += 1
    # soft procedure, unconstrained stage 1: w_s = w_TB, stage 2 is the joint problem in tracking form
    wTB = np.linalg.solve(d["gamma"] * d["SEE"], d["muE"])
    xs, _, _ = solve(d, track=wTB)
    check(np.max(np.abs(xs - xJ)) < 5 * TOL, f"part 4: soft procedure with an unconstrained stage 1 is inexact on instance {it}")
    counts["p4s"] += 1
    # soft procedure with the one-sided stage 1: tilt nu = -zeta*, loss within nu'(w_J - w_2)
    xs2, _, _ = solve(d, track=wst)
    Ls = J - jointvalue(d, xs2)
    wJ = xJ[N:] + d["Q"] @ xJ[:N]; w2 = xs2[N:] + d["Q"] @ xs2[:N]
    check(-1e-7 <= Ls <= (-zst) @ (wJ - w2) + 1e-7, f"part 4: soft loss {Ls:.2e} outside [0, nu'(w_J - w_2)] = {(-zst) @ (wJ - w2):.2e} on instance {it}")
    counts["p4b"] += 1

print("cases:", counts)
check(counts["p1z"] >= 20 and counts["p2T"] >= 20 and counts["p2z"] >= 20 and counts["p3"] >= 30 and counts["p4x"] >= 5 and counts["p4"] - counts["p4x"] >= 5,
      "too few instances exercised a part")
if FAIL:
    print(f"{len(FAIL)} check(s) failed"); sys.exit(1)
print("all checks passed")
