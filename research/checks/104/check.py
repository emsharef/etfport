"""Solver checks of claim 104 (M7, one review): two-stage exactness and loss in the inputs (refile of 103
with the joint-optimality criterion of 2b), including red's counterexample to claim 103 as a fixed instance.

Random assumed instances solved with cvxpy/CLARABEL (floating point, not a certificate). Exits
non-zero on failure. A check, not a proof. Run: uv run python checks/104/check.py
"""
import sys
import numpy as np
import cvxpy as cp

rng = np.random.default_rng(103)
FAIL = []
TOL = 3e-6   # objective values are of order 1e-3 to 1e-2


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


def cost_expr(x, d):
    u = x - d["xm"]
    return cp.sum(cp.multiply(d["kp"], cp.pos(u)) + cp.multiply(d["km"], cp.pos(-u)))


def base_cons(x, d):
    return [x >= 0, x <= d["xbar"], d["h"] - cp.sum(x - d["xm"]) - cost_expr(x, d) >= 0]


def solve_joint(d):
    x = cp.Variable(d["n"])
    obj = d["mu"] @ x - 0.5 * cp.quad_form(x, cp.psd_wrap(d["Sig"])) - cost_expr(x, d)
    p = cp.Problem(cp.Maximize(obj), base_cons(x, d)); p.solve(solver=cp.CLARABEL)
    return np.array(x.value).ravel(), p.value


def stage1(d):
    """maximize G(b) over B_F = b(F): b = B'x, x in F."""
    x = cp.Variable(d["n"]); b = d["B"].T @ x
    G = d["lam"] @ b - 0.5 * d["gamma"] * cp.quad_form(b, cp.psd_wrap(d["Sft"]))
    p = cp.Problem(cp.Maximize(G), base_cons(x, d)); p.solve(solver=cp.CLARABEL)
    return d["B"].T @ np.array(x.value).ravel(), p.value


def stage2_fibre(d, bstar):
    x = cp.Variable(d["n"])
    H = d["alpha"] @ x[:d["N"]] - d["cE"] @ x[d["N"]:] - 0.5 * d["gamma"] * (
        cp.quad_form(x[:d["N"]], cp.psd_wrap(np.diag(d["v"]))) + cp.quad_form(x[d["N"]:], cp.psd_wrap(np.diag(d["SE"])))) - cost_expr(x, d)
    p = cp.Problem(cp.Maximize(H), base_cons(x, d) + [d["B"].T @ x == bstar]); p.solve(solver=cp.CLARABEL)
    return np.array(x.value).ravel(), p.value


def stage2_soft(d, bstar):
    x = cp.Variable(d["n"]); b = d["B"].T @ x
    S = d["alpha"] @ x[:d["N"]] - d["cE"] @ x[d["N"]:] - 0.5 * d["gamma"] * (
        cp.quad_form(x[:d["N"]], cp.psd_wrap(np.diag(d["v"]))) + cp.quad_form(x[d["N"]:], cp.psd_wrap(np.diag(d["SE"])))
        + cp.quad_form(b - bstar, cp.psd_wrap(d["Sft"]))) - cost_expr(x, d)
    p = cp.Problem(cp.Maximize(S), base_cons(x, d)); p.solve(solver=cp.CLARABEL)
    return np.array(x.value).ravel()


def Q(d, x):
    return d["mu"] @ x - 0.5 * x @ d["Sig"] @ x - np.sum(d["kp"] * np.maximum(x - d["xm"], 0) + d["km"] * np.maximum(d["xm"] - x, 0))


def instance(N, M, K, frictionless, unreachable=False):
    BA = rng.uniform(-0.3, 1.3, (N, K))
    if unreachable:
        BE = np.array([[1.0, 0.0]])                 # reachable = first factor only
        BA[1:, 1] = 0.0                              # other funds reachable
        BA[0, 1] = rng.uniform(0.5, 1.5)             # fund 0 carries the unreachable direction
    else:
        BE = rng.uniform(0.5, 1.5, (M, K)) * (np.eye(K) + 0.2 * rng.uniform(0, 1, (K, K)))
    Sf = np.diag(rng.uniform(0.002, 0.01, K)); Pl = np.diag(rng.uniform(0.0, 0.001, K))
    Sft = Sf + Pl
    if unreachable:
        Sft = Sft + 0.3 * np.sqrt(np.outer(np.diag(Sft), np.diag(Sft))) * (1 - np.eye(K))   # correlated factors so the hedge matters
    v = rng.uniform(0.0005, 0.004, N)
    SE = np.zeros(M) if frictionless else rng.uniform(0.0, 0.0004, M)
    cE = np.zeros(M) if frictionless else rng.uniform(-0.0005, 0.001, M)
    lam = rng.uniform(0.005, 0.04, K); alpha = rng.uniform(-0.01, 0.015, N)
    kpA = rng.uniform(0.0, 0.01, N); kmA = rng.uniform(0.0, 0.01, N)
    kpE = np.zeros(M) if frictionless else rng.uniform(0.0, 0.002, M)
    kmE = np.zeros(M) if frictionless else rng.uniform(0.0, 0.002, M)
    gamma = rng.uniform(2.0, 6.0)
    B = np.vstack([BA, BE])
    Sig = B @ Sft @ B.T + np.diag(np.concatenate([v, SE]))
    mu = np.concatenate([alpha + BA @ lam, BE @ lam - cE])
    xm = np.concatenate([rng.uniform(0.0, 0.5, N), rng.uniform(0.2, 2.0, M)])
    return dict(N=N, M=M, K=K, n=N + M, BA=BA, BE=BE, B=B, Sft=Sft, v=v, SE=SE, cE=cE, lam=lam, alpha=alpha,
                kp=np.concatenate([kpA, kpE]), km=np.concatenate([kmA, kmE]), gamma=gamma, Sig=gamma * Sig, Sigraw=Sig,
                mu=mu, xm=xm, xbar=np.full(N + M, 5.0), h=100.0)


counts = {"2a": 0, "2b_exact": 0, "2b_loss": 0, "3a": 0, "2c": 0, "3d": 0}

# (i) frictionless spanning: both losses zero
for it in range(30):
    d = instance(3, 2, 2, frictionless=True)
    xJ, J = solve_joint(d)
    if np.any(xJ[d["N"]:] < 1e-4):
        continue
    bstar, _ = stage1(d)
    x2, _ = stage2_fibre(d, bstar)
    xs = stage2_soft(d, bstar)
    check(J - Q(d, x2) < 20 * TOL, f"2a: fibre-confined loss {J - Q(d, x2):.2e} not zero, instance {it}")
    check(J - Q(d, xs) < 20 * TOL, f"2a: soft loss {J - Q(d, xs):.2e} not zero, instance {it}")
    counts["2a"] += 1

# (ii) red's counterexample to claim 103: self-band holds, fund band fails, two-stage loses
def ce_instance():
    g = 5.0; Sft = np.array([[0.0854 ** 2]]); lam = np.array([0.0184]); v = np.array([0.02 ** 2])
    BA = np.array([[1.0]]); BE = np.array([[1.0]]); B = np.vstack([BA, BE])
    xmA = 0.10; alpha = np.array([0.0030 + g * v[0] * xmA])           # fund marginal alpha - gamma v x^- = 30 bp
    bTB = float(lam[0] / (g * Sft[0, 0])); xmE = bTB - xmA               # incumbent exposure equals b_TB
    Sig = B @ Sft @ B.T + np.diag(np.concatenate([v, [0.0]]))
    mu = np.concatenate([alpha + BA @ lam, BE @ lam])
    return dict(N=1, M=1, K=1, n=2, BA=BA, BE=BE, B=B, Sft=Sft, v=v, SE=np.zeros(1), cE=np.zeros(1), lam=lam, alpha=alpha,
                kp=np.array([0.0010, 0.0050]), km=np.array([0.0010, 0.0050]), gamma=g, Sig=g * Sig, mu=mu,
                xm=np.array([xmA, xmE]), xbar=np.array([5.0, 5.0]), h=10.0)
d = ce_instance()
xJ, J = solve_joint(d); bstar, _ = stage1(d); x2, _ = stage2_fibre(d, bstar)
loss_ce = J - Q(d, x2)
print(f"counterexample: joint fund {xJ[0]:.4f}, ETF {xJ[1]:.4f}; two-stage fund {x2[0]:.4f}, ETF {x2[1]:.4f}; loss {loss_ce:.3e}")
check(abs(x2[0] - d["xm"][0]) < 1e-4 and abs(x2[1] - d["xm"][1]) < 1e-4, "counterexample: stage 2 should hold both positions")
check(xJ[0] > d["xm"][0] + 0.03 and abs(xJ[1] - d["xm"][1]) < 1e-3, "counterexample: joint optimum should buy the fund and leave the ETF")
check(4e-5 < loss_ce < 7e-5, f"counterexample: loss {loss_ce:.2e} not about 5.2e-5")
fund_marg = d["alpha"][0] - d["gamma"] * d["v"][0] * x2[0]
check(fund_marg > d["kp"][0] + 1e-6, "counterexample: the fund band should fail at x_2")

# (ii-b) red's capped-fund counterexample to claim 104's 3b: the bound needs the normal-cone term
def capped_instance():
    g = 5.0; Sft = np.array([[0.0073, 0.001], [0.001, 0.0037]]); lam = np.array([0.0184, -0.004])
    BA = np.array([[0.8, 0.5]]); BE = np.array([[1.0, 0.0]]); B = np.vstack([BA, BE])
    v = np.array([4e-4]); alpha = np.array([0.03])
    Sig = B @ Sft @ B.T + np.diag(np.concatenate([v, [0.0]]))
    mu = np.concatenate([alpha + BA @ lam, BE @ lam])
    return dict(N=1, M=1, K=2, n=2, BA=BA, BE=BE, B=B, Sft=Sft, v=v, SE=np.zeros(1), cE=np.zeros(1), lam=lam, alpha=alpha,
                kp=np.array([0.001, 0.0]), km=np.array([0.001, 0.0]), gamma=g, Sig=g * Sig, mu=mu,
                xm=np.array([0.1, 1.0]), xbar=np.array([0.3, 5.0]), h=100.0)
d = capped_instance()
xJ, J = solve_joint(d); bstar, _ = stage1(d); x2, _ = stage2_fibre(d, bstar)
loss_cap = J - Q(d, x2)
S = d["Sft"]; SRR, SRU, SUU = S[0, 0], S[0, 1], S[1, 1]; SUR_dot = SUU - SRU * SRU / SRR
u = d["BA"][0, 1]; Jlam = d["lam"][1] - SRU / SRR * d["lam"][0]; g = d["gamma"]
a_red = d["alpha"][0] + u * Jlam; s_red = d["v"][0] + u * u * SUR_dot
a_star = np.clip(u * Jlam / (g * u * u * SUR_dot), 0.0, d["xbar"][0])
lo, hi = (a_red - d["kp"][0]) / (g * s_red), (a_red + d["km"][0]) / (g * s_red)
a_J = np.clip(np.clip(d["xm"][0], lo, hi), 0.0, d["xbar"][0])
mJ = a_red - g * s_red * a_J; muJ = max(0.0, mJ - d["kp"][0], -d["km"][0] - mJ)
old_bound = 0.5 * g * s_red * (a_J - a_star) ** 2 + (d["kp"][0] + d["km"][0]) * abs(a_J - a_star)
new_bound = old_bound + muJ * abs(a_J - a_star)
low = 0.5 * g * s_red * (a_J - a_star) ** 2
print(f"capped instance: a_J {a_J:.3f} (joint {xJ[0]:.3f}), a* {a_star:.3f} (two-stage {x2[0]:.3f}), loss {loss_cap:.3e}, old bound {old_bound:.3e}, corrected bound {new_bound:.3e}, lower {low:.3e}, mu_J {muJ:.4f}")
check(abs(xJ[0] - a_J) < 2e-4 and abs(x2[0] - a_star) < 2e-4 and a_J > d["xbar"][0] - 1e-6, "capped instance: holdings differ from the closed forms or a_J not at the cap")
check(loss_cap > old_bound, "capped instance: the uncorrected bound should fail here")
check(low - 1e-9 <= loss_cap <= new_bound + 1e-9, "capped instance: corrected 3b bracket fails")
check(x2[1] > 1e-3 and xJ[1] > 1e-3, "capped instance: the ETF should stay interior")

# (iii) frictions: identity, L_E bound, the joint criterion of 2b (self-band AND fund bands)
for it in range(60):
    d = instance(3, 2, 2, frictionless=False)
    xJ, J = solve_joint(d)
    if np.any(xJ[d["N"]:] < 1e-4):
        continue
    bstar, Gstar = stage1(d)
    x2, V2 = stage2_fibre(d, bstar)
    if np.any(x2[d["N"]:] < 1e-4):
        continue
    lam_loss = J - Q(d, x2)
    check(lam_loss >= -20 * TOL, f"3a: negative loss {lam_loss:.2e}, instance {it}")
    R = np.linalg.inv(d["BE"]); g = d["gamma"]
    Sft_ih = np.linalg.inv(np.linalg.cholesky(d["Sft"]))
    LE = np.linalg.norm(Sft_ih @ R, 2) * (np.linalg.norm(d["cE"]) + g * np.max(d["SE"]) * np.linalg.norm(d["xbar"][d["N"]:]) + np.linalg.norm(np.maximum(d["kp"][d["N"]:], d["km"][d["N"]:])))
    check(lam_loss <= LE ** 2 / (2 * g) + 20 * TOL, f"3a: loss {lam_loss:.2e} exceeds L_E^2/(2 gamma), instance {it}")
    counts["3a"] += 1
    N = d["N"]; MARG = 3e-5
    def in_band(val, u, kp, km, at_zero=False, at_cap=False, strict=True):
        m = MARG if strict else -MARG
        if u > 1e-4:
            return abs(val - kp) < (1e-4 if not strict else 1e-4)
        if u < -1e-4:
            return abs(val + km) < 1e-4
        if at_zero:
            return val <= kp - m
        if at_cap:
            return val >= -km + m
        return (-km + m <= val <= kp - m)
    etf_ok = all(in_band(-d["cE"][j] - g * d["SE"][j] * x2[N + j], x2[N + j] - d["xm"][N + j], d["kp"][N + j], d["km"][N + j]) for j in range(d["M"]))
    fund_ok = all(in_band(d["alpha"][i] - g * d["v"][i] * x2[i], x2[i] - d["xm"][i], d["kp"][i], d["km"][i], at_zero=x2[i] < 1e-4, at_cap=x2[i] > d["xbar"][i] - 1e-4) for i in range(N))
    etf_viol = any((not in_band(-d["cE"][j] - g * d["SE"][j] * x2[N + j], x2[N + j] - d["xm"][N + j], d["kp"][N + j], d["km"][N + j], strict=False)) for j in range(d["M"]))
    fund_viol = any((not in_band(d["alpha"][i] - g * d["v"][i] * x2[i], x2[i] - d["xm"][i], d["kp"][i], d["km"][i], at_zero=x2[i] < 1e-4, at_cap=x2[i] > d["xbar"][i] - 1e-4, strict=False)) for i in range(N))
    if etf_ok and fund_ok:
        check(lam_loss < 50 * TOL, f"2b: joint criterion holds at x_2 but loss {lam_loss:.2e} > 0, instance {it}")
        counts["2b_exact"] += 1
    elif etf_viol or fund_viol:
        check(lam_loss > TOL, f"2b: joint criterion fails at x_2 (etf {etf_viol}, fund {fund_viol}) but loss {lam_loss:.2e} is zero, instance {it}")
        counts["2b_loss"] += 1
    if lam_loss < TOL:
        check(not etf_viol, f"2b necessity: zero loss but the ETF self-band fails, instance {it}")

# (iii) one unreachable fund, everything else frictionless
for it in range(40):
    d = instance(3, 1, 2, frictionless=True, unreachable=True)
    xJ, J = solve_joint(d)
    if np.any(xJ[d["N"]:] < 1e-4):
        continue
    bstar, _ = stage1(d)
    x2, _ = stage2_fibre(d, bstar)
    lam_loss = J - Q(d, x2)
    if np.any(x2[d["N"]:] < 1e-4) or np.any(x2[1:d["N"]] > d["xbar"][1:d["N"]] - 1e-4) or np.any(xJ[1:d["N"]] > d["xbar"][1:d["N"]] - 1e-4):
        print(f"   (2c instance {it} skipped: a bound binds on the fibre; ETF {x2[d['N']:]}, funds {x2[:d['N']]})")
        continue   # outside 2c's hypothesis (ETF bounds slack on both solutions)
    # reduced moments: reachable subspace = e_1, unreachable = e_2
    S = d["Sft"]; SRR, SRU, SUU = S[0, 0], S[0, 1], S[1, 1]
    SUR_dot = SUU - SRU * SRU / SRR
    u = d["BA"][0, 1]
    Jlam = d["lam"][1] - SRU / SRR * d["lam"][0]          # J' lambda in the unreachable coordinate
    g = d["gamma"]
    a_red = d["alpha"][0] + u * Jlam
    s_red = d["v"][0] + u * u * SUR_dot
    a_star = np.clip(u * Jlam / (g * u * u * SUR_dot), 0.0, d["xbar"][0])
    lo, hi = (a_red - d["kp"][0]) / (g * s_red), (a_red + d["km"][0]) / (g * s_red)
    a_J = np.clip(np.clip(d["xm"][0], lo, hi), 0.0, d["xbar"][0])
    def psi(a):
        return a_red * a - 0.5 * g * s_red * a * a - d["kp"][0] * max(a - d["xm"][0], 0) - d["km"][0] * max(d["xm"][0] - a, 0)
    check(abs(xJ[0] - a_J) < 2e-4, f"2c: joint fund holding {xJ[0]:.5f} differs from band clip {a_J:.5f}, instance {it}")
    check(abs(x2[0] - a_star) < 2e-4, f"2c: two-stage fund holding {x2[0]:.5f} differs from a* {a_star:.5f}, instance {it}")
    check(abs(lam_loss - (psi(a_J) - psi(a_star))) < 30 * TOL, f"2c: loss {lam_loss:.3e} differs from psi gap {psi(a_J) - psi(a_star):.3e}, instance {it}")
    mJ = a_red - g * s_red * a_J; muJ = max(0.0, mJ - d["kp"][0], -d["km"][0] - mJ)
    gap = psi(a_J) - psi(a_star); dlt = abs(a_J - a_star)
    check(0.5 * g * s_red * dlt ** 2 - 1e-9 <= gap <= 0.5 * g * s_red * dlt ** 2 + (d["kp"][0] + d["km"][0] + muJ) * dlt + 1e-9,
          f"3b: corrected bracket fails, instance {it}")
    counts["2c"] += 1

# (iv) soft procedure: nu = 0 when b_TB feasible; multiplier bound otherwise
for it in range(40):
    d = instance(3, 2, 2, frictionless=(it % 2 == 0))
    xJ, J = solve_joint(d)
    bstar, _ = stage1(d)
    nu = d["lam"] - d["gamma"] * d["Sft"] @ bstar
    xs = stage2_soft(d, bstar)
    lam_s = J - Q(d, xs)
    bJ, b2 = d["B"].T @ xJ, d["B"].T @ xs
    check(lam_s >= -20 * TOL and lam_s <= nu @ (bJ - b2) + 30 * TOL, f"3d: soft loss {lam_s:.2e} violates the multiplier bound {nu @ (bJ - b2):.2e}, instance {it}")
    if np.linalg.norm(nu) < 1e-6:
        check(lam_s < 30 * TOL, f"3d: nu = 0 but soft loss {lam_s:.2e}, instance {it}")
    counts["3d"] += 1

print("cases:", counts)
check(counts["2a"] >= 10 and counts["3a"] >= 10 and counts["2c"] >= 10 and counts["3d"] >= 10 and counts["2b_loss"] >= 5, "too few instances exercised a part")
if FAIL:
    print(f"{len(FAIL)} check(s) failed"); sys.exit(1)
print("all checks passed")
