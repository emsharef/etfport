"""Solver checks of claim 103 (M7, one review): two-stage exactness and loss in the inputs.

Random assumed instances solved with cvxpy/CLARABEL (floating point, not a certificate). Exits
non-zero on failure. A check, not a proof. Run: uv run python checks/103/check.py
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


counts = {"2a": 0, "2b_exact": 0, "3a": 0, "2c": 0, "3d": 0}

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

# (ii) frictions: identity, L_E bound, self-band test
for it in range(40):
    d = instance(3, 2, 2, frictionless=False)
    xJ, J = solve_joint(d)
    if np.any(xJ[d["N"]:] < 1e-4):
        continue
    bstar, Gstar = stage1(d)
    x2, V2 = stage2_fibre(d, bstar)
    lam_loss = J - Q(d, x2)
    check(lam_loss >= -20 * TOL, f"3a: negative loss {lam_loss:.2e}, instance {it}")
    R = np.linalg.inv(d["BE"]); g = d["gamma"]
    Sft_ih = np.linalg.inv(np.linalg.cholesky(d["Sft"]))    # Sft^{-1/2} up to rotation
    LE = np.linalg.norm(Sft_ih @ R, 2) * (np.linalg.norm(d["cE"]) + g * np.max(d["SE"]) * np.linalg.norm(d["xbar"][d["N"]:]) + np.linalg.norm(np.maximum(d["kp"][d["N"]:], d["km"][d["N"]:])))
    check(lam_loss <= LE ** 2 / (2 * g) + 20 * TOL, f"3a: loss {lam_loss:.2e} exceeds L_E^2/(2 gamma) = {LE**2/(2*g):.2e}, instance {it}")
    counts["3a"] += 1
    # self-band condition at x2: is there t in the trade-sign sets with -cE - g SE x2E - t = 0 ?
    N = d["N"]; ok = True
    for j in range(d["M"]):
        val = -d["cE"][j] - g * d["SE"][j] * x2[N + j]
        u = x2[N + j] - d["xm"][N + j]
        if u > 1e-4:
            ok &= abs(val - d["kp"][N + j]) < 1e-4
        elif u < -1e-4:
            ok &= abs(val + d["km"][N + j]) < 1e-4
        else:
            ok &= (-d["km"][N + j] - 1e-4 <= val <= d["kp"][N + j] + 1e-4)
    if ok:
        check(lam_loss < 50 * TOL, f"2b: self-band holds but loss {lam_loss:.2e} > 0, instance {it}")
        counts["2b_exact"] += 1
    elif lam_loss < TOL:
        # zero loss without the condition would contradict 2b (allow solver slack at the band edges)
        check(False, f"2b: zero loss but self-band condition fails, instance {it}")

# (iii) one unreachable fund, everything else frictionless
for it in range(40):
    d = instance(3, 1, 2, frictionless=True, unreachable=True)
    xJ, J = solve_joint(d)
    if np.any(xJ[d["N"]:] < 1e-4) or xJ[0] > d["xbar"][0] - 1e-4:
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
check(counts["2a"] >= 10 and counts["3a"] >= 10 and counts["2c"] >= 10 and counts["3d"] >= 10, "too few instances exercised a part")
if FAIL:
    print(f"{len(FAIL)} check(s) failed"); sys.exit(1)
print("all checks passed")
