"""Solver checks of claim 106 (M7, one review): the cost of the ETF-only restriction in the inputs.

Random assumed instances solved with cvxpy/CLARABEL (floating point, not a certificate). Exits
non-zero on failure. A check, not a proof. Run: uv run python checks/106/check.py
"""
import sys
import numpy as np
import cvxpy as cp

rng = np.random.default_rng(106)
FAIL = []
TOL = 3e-6


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


def cost_expr(x, d):
    u = x - d["xm"]
    return cp.sum(cp.multiply(d["kp"], cp.pos(u)) + cp.multiply(d["km"], cp.pos(-u)))


def solve_class(d, cls):
    x = cp.Variable(d["n"]); N = d["N"]
    obj = d["mu"] @ x - 0.5 * cp.quad_form(x, cp.psd_wrap(d["Sig"])) - cost_expr(x, d)
    cons = [x >= 0, x <= d["xbar"], d["h"] - cp.sum(x - d["xm"]) - cost_expr(x, d) >= 0]
    if cls == "E0":
        cons.append(x[:N] == d["xm"][:N])
    elif cls == "Em":
        cons.append(x[:N] <= d["xm"][:N])
    p = cp.Problem(cp.Maximize(obj), cons); p.solve(solver=cp.CLARABEL)
    return np.array(x.value).ravel(), p.value


def instance(N, M, K, frictionless, unreachable=False):
    BA = rng.uniform(-0.3, 1.3, (N, K))
    if unreachable:
        BE = np.array([[1.0, 0.0]]); BA[1:, 1] = 0.0; BA[0, 1] = rng.uniform(0.5, 1.5)
    else:
        BE = rng.uniform(0.5, 1.5, (M, K)) * (np.eye(K) + 0.2 * rng.uniform(0, 1, (K, K)))
    Sft = np.diag(rng.uniform(0.002, 0.01, K)) + np.diag(rng.uniform(0.0, 0.001, K))
    Sft = Sft + 0.3 * np.sqrt(np.outer(np.diag(Sft), np.diag(Sft))) * (1 - np.eye(K))
    v = rng.uniform(0.0005, 0.004, N)
    cE = np.zeros(M) if frictionless else rng.uniform(-0.0005, 0.001, M)
    lam = rng.uniform(0.005, 0.04, K); alpha = rng.uniform(-0.012, 0.018, N)
    kpA = rng.uniform(0.0, 0.01, N); kmA = rng.uniform(0.0, 0.01, N)
    kpE = np.zeros(M) if frictionless else rng.uniform(0.0, 0.002, M)
    kmE = np.zeros(M) if frictionless else rng.uniform(0.0, 0.002, M)
    gamma = rng.uniform(2.0, 6.0)
    B = np.vstack([BA, BE])
    Sig = gamma * (B @ Sft @ B.T + np.diag(np.concatenate([v, np.zeros(M)])))
    mu = np.concatenate([alpha + BA @ lam, BE @ lam - cE])
    xm = np.concatenate([rng.uniform(0.0, 0.4, N), rng.uniform(0.5, 2.5, M)])
    return dict(N=N, M=M, K=K, n=N + M, BA=BA, BE=BE, B=B, Sft=Sft, v=v, cE=cE, lam=lam, alpha=alpha,
                kp=np.concatenate([kpA, kpE]), km=np.concatenate([kmA, kmE]), gamma=gamma, Sig=Sig, mu=mu,
                xm=xm, xbar=np.full(N + M, 5.0), h=100.0)


def interior(d, x):
    return np.all(x[d["N"]:] > 1e-3) and np.all(x[d["N"]:] < d["xbar"][d["N"]:] - 1e-3)


def psi(d, i, a, alpha_i=None, v_i=None):
    al = d["alpha"][i] if alpha_i is None else alpha_i
    vv = d["v"][i] if v_i is None else v_i
    return al * a - 0.5 * d["gamma"] * vv * a * a - d["kp"][i] * max(a - d["xm"][i], 0) - d["km"][i] * max(d["xm"][i] - a, 0)


def closed_forms(d, alpha, v):
    """part 2 (or 3 with reduced moments): C^- and J^- - J^0 in closed form."""
    g = d["gamma"]; N = d["N"]; Cm = 0.0; S = 0.0
    for i in range(N):
        lo = (alpha[i] - d["kp"][i]) / (g * v[i]); hi = (alpha[i] + d["km"][i]) / (g * v[i])
        p = alpha[i] - d["kp"][i] - g * v[i] * d["xm"][i]; s = g * v[i] * d["xm"][i] - alpha[i] - d["km"][i]
        if p > 0:
            Cm += p * p / (2 * g * v[i]) if lo <= d["xbar"][i] else psi(d, i, d["xbar"][i], alpha[i], v[i]) - psi(d, i, d["xm"][i], alpha[i], v[i])
        if s > 0:
            S += s * s / (2 * g * v[i]) if hi >= 0 else psi(d, i, 0.0, alpha[i], v[i]) - psi(d, i, d["xm"][i], alpha[i], v[i])
    return Cm, S


counts = {"p2": 0, "p3": 0, "p4": 0, "p1": 0}

# (i) spanning frictionless: closed forms; (iv) structure
for it in range(60):
    d = instance(3, 2, 2, frictionless=True)
    xJ, J = solve_class(d, "F"); xm_, Jm = solve_class(d, "Em"); x0, J0 = solve_class(d, "E0")
    if not (interior(d, xJ) and interior(d, xm_) and interior(d, x0)):
        continue
    Cm, S = closed_forms(d, d["alpha"], d["v"])
    check(abs((J - Jm) - Cm) < 10 * TOL, f"part 2: C^- {J - Jm:.3e} differs from the closed form {Cm:.3e}, instance {it}")
    check(abs((Jm - J0) - S) < 10 * TOL, f"part 2: J^- - J^0 {Jm - J0:.3e} differs from the closed form {S:.3e}, instance {it}")
    bought = np.any(xJ[:d["N"]] > d["xm"][:d["N"]] + 1e-4); traded = np.any(np.abs(xJ[:d["N"]] - d["xm"][:d["N"]]) > 1e-4)
    check((J - Jm > 10 * TOL) == bought, f"part 1: C^- zero-ness disagrees with purchases at the optimum, instance {it}")
    check((J - J0 > 10 * TOL) == traded, f"part 1: C^0 zero-ness disagrees with trades at the optimum, instance {it}")
    counts["p2"] += 1; counts["p1"] += 1

# (ii) one unreachable fund: reduced forms
for it in range(60):
    d = instance(3, 1, 2, frictionless=True, unreachable=True)
    xJ, J = solve_class(d, "F"); xm_, Jm = solve_class(d, "Em"); x0, J0 = solve_class(d, "E0")
    if not (interior(d, xJ) and interior(d, xm_) and interior(d, x0)) or xJ[0] > d["xbar"][0] - 1e-3:
        continue
    S_ = d["Sft"]; SRR, SRU, SUU = S_[0, 0], S_[0, 1], S_[1, 1]; SUR_dot = SUU - SRU * SRU / SRR
    u = d["BA"][0, 1]; Jlam = d["lam"][1] - SRU / SRR * d["lam"][0]
    alpha = d["alpha"].copy(); v = d["v"].copy()
    alpha[0] = d["alpha"][0] + u * Jlam; v[0] = d["v"][0] + u * u * SUR_dot
    Cm, S = closed_forms(d, alpha, v)
    check(abs((J - Jm) - Cm) < 10 * TOL, f"part 3: C^- {J - Jm:.3e} differs from the reduced closed form {Cm:.3e}, instance {it}")
    check(abs((Jm - J0) - S) < 10 * TOL, f"part 3: J^- - J^0 {Jm - J0:.3e} differs from the reduced closed form {S:.3e}, instance {it}")
    counts["p3"] += 1

# (iii) ETF frictions, Sigma_E = 0: brackets
for it in range(80):
    d = instance(3, 2, 2, frictionless=False)
    xJ, J = solve_class(d, "F"); xm_, Jm = solve_class(d, "Em"); x0, J0 = solve_class(d, "E0")
    if not (interior(d, xJ) and interior(d, xm_) and interior(d, x0)):
        continue
    R = np.linalg.inv(d["BE"]); g = d["gamma"]; N = d["N"]
    lo_sum = hi_sum = lo_s = hi_s = 0.0
    for i in range(N):
        r = R.T @ d["BA"][i]
        hp = np.sum(np.maximum(r, 0) * d["km"][N:] + np.maximum(-r, 0) * d["kp"][N:])
        hm = np.sum(np.maximum(r, 0) * d["kp"][N:] + np.maximum(-r, 0) * d["km"][N:])
        A0 = d["alpha"][i] + r @ d["cE"] - g * d["v"][i] * d["xm"][i]
        def gain(m, dmax, vi=d["v"][i]):
            # max over delta in [0, dmax] of m delta - (gamma v/2) delta^2: the cap or floor adjustment
            if m <= 0:
                return 0.0
            dstar = m / (g * vi)
            return m * m / (2 * g * vi) if dstar <= dmax else m * dmax - 0.5 * g * vi * dmax * dmax
        room_up = d["xbar"][i] - d["xm"][i]; room_dn = d["xm"][i]
        lo_sum += gain(A0 - d["kp"][i] - hp, room_up)
        hi_sum += gain(A0 - d["kp"][i] + hm, room_up)
        lo_s += gain(-A0 - d["km"][i] - hm, room_dn)
        hi_s += gain(-A0 - d["km"][i] + hp, room_dn)
    check(lo_sum - 10 * TOL <= J - Jm <= hi_sum + 10 * TOL, f"part 4: C^- {J - Jm:.3e} outside [{lo_sum:.3e}, {hi_sum:.3e}], instance {it}")
    check(lo_s - 10 * TOL <= Jm - J0 <= hi_s + 10 * TOL, f"part 4: sales value {Jm - J0:.3e} outside [{lo_s:.3e}, {hi_s:.3e}], instance {it}")
    counts["p4"] += 1

print("cases:", counts)
check(counts["p2"] >= 15 and counts["p3"] >= 10 and counts["p4"] >= 15, "too few instances exercised a part")
if FAIL:
    print(f"{len(FAIL)} check(s) failed"); sys.exit(1)
print("all checks passed")
