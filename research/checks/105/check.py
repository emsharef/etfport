"""Solver checks of claim 105 (M7, one review): how premium error enters fund choice.

Random assumed instances solved with cvxpy/CLARABEL (floating point, not a certificate). Exits
non-zero on failure. A check, not a proof. Run: uv run python checks/105/check.py
"""
import sys
import numpy as np
import cvxpy as cp

rng = np.random.default_rng(105)
FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


def cost_expr(x, d):
    u = x - d["xm"]
    return cp.sum(cp.multiply(d["kp"], cp.pos(u)) + cp.multiply(d["km"], cp.pos(-u)))


def solve_joint(d, lam, fix_funds=None):
    mu = np.concatenate([d["alpha"] + d["BA"] @ lam, d["BE"] @ lam])
    x = cp.Variable(d["n"])
    obj = mu @ x - 0.5 * cp.quad_form(x, cp.psd_wrap(d["Sig"])) - cost_expr(x, d)
    cons = [x >= 0, x <= d["xbar"], d["h"] - cp.sum(x - d["xm"]) - cost_expr(x, d) >= 0]
    if fix_funds is not None:
        cons.append(x[:d["N"]] == fix_funds)
    p = cp.Problem(cp.Maximize(obj), cons); p.solve(solver=cp.CLARABEL)
    return np.array(x.value).ravel(), p.value


def instance(N, M, K, unreachable=False):
    BA = rng.uniform(-0.3, 1.3, (N, K))
    if unreachable:
        BE = np.array([[1.0, 0.0]]); BA[1:, 1] = 0.0; BA[0, 1] = rng.uniform(0.5, 1.5)
    else:
        BE = rng.uniform(0.5, 1.5, (M, K)) * (np.eye(K) + 0.2 * rng.uniform(0, 1, (K, K)))
    Sft = np.diag(rng.uniform(0.002, 0.01, K)) + np.diag(rng.uniform(0.0, 0.001, K))
    Sft = Sft + 0.3 * np.sqrt(np.outer(np.diag(Sft), np.diag(Sft))) * (1 - np.eye(K))
    v = rng.uniform(0.0005, 0.004, N)
    lam = rng.uniform(0.005, 0.04, K); alpha = rng.uniform(-0.01, 0.015, N)
    kpA = rng.uniform(0.0, 0.01, N); kmA = rng.uniform(0.0, 0.01, N)
    gamma = rng.uniform(2.0, 6.0)
    B = np.vstack([BA, BE])
    Sig = gamma * (B @ Sft @ B.T + np.diag(np.concatenate([v, np.zeros(M)])))
    xm = np.concatenate([rng.uniform(0.0, 0.5, N), rng.uniform(0.2, 2.0, M)])
    return dict(N=N, M=M, K=K, n=N + M, BA=BA, BE=BE, B=B, Sft=Sft, v=v, lam=lam, alpha=alpha,
                kp=np.concatenate([kpA, np.zeros(M)]), km=np.concatenate([kmA, np.zeros(M)]), gamma=gamma,
                Sig=Sig, xm=xm, xbar=np.full(N + M, 5.0), h=100.0)


def interior_etfs(d, x):
    return np.all(x[d["N"]:] > 1e-4) and np.all(x[d["N"]:] < d["xbar"][d["N"]:] - 1e-4)


counts = {"p1": 0, "p2": 0, "p2flip": 0, "p3": 0}

# (i) spanning: fund holdings invariant to premium perturbations; exposure moves
for it in range(30):
    d = instance(3, 2, 2)
    x0, _ = solve_joint(d, d["lam"])
    if not interior_etfs(d, x0):
        continue
    for k in range(3):
        e = rng.normal(0, 0.005, d["K"])
        x1, _ = solve_joint(d, d["lam"] + e)
        if not interior_etfs(d, x1):
            continue
        check(np.max(np.abs(x1[:d["N"]] - x0[:d["N"]])) < 3e-4, f"part 1: fund holdings moved with the premium, instance {it}")
        y0, y1 = d["B"].T @ x0, d["B"].T @ x1
        ystar = np.linalg.solve(d["gamma"] * d["Sft"], e)
        check(np.max(np.abs((y1 - y0) - ystar)) < 3e-3, f"part 1: exposure move differs from the Markowitz shift, instance {it}")
        counts["p1"] += 1

# (ii) one unreachable fund: closed form along a premium line, gradient, flip test, loss bracket
def reduced(d, lam):
    S = d["Sft"]; SRR, SRU, SUU = S[0, 0], S[0, 1], S[1, 1]
    SUR_dot = SUU - SRU * SRU / SRR
    u = d["BA"][0, 1]; Jlam = lam[1] - SRU / SRR * lam[0]
    a_red = d["alpha"][0] + u * Jlam; s_red = d["v"][0] + u * u * SUR_dot
    g = d["gamma"]
    lo, hi = (a_red - d["kp"][0]) / (g * s_red), (a_red + d["km"][0]) / (g * s_red)
    a = np.clip(np.clip(d["xm"][0], lo, hi), 0.0, d["xbar"][0])
    Jvec = np.array([-SRU / SRR, 1.0]) * u          # B^A_i J' as a vector on lambda
    return a, a_red, s_red, Jvec


for it in range(40):
    d = instance(3, 1, 2, unreachable=True)
    xt, Jt = solve_joint(d, d["lam"])
    if not interior_etfs(d, xt) or xt[0] > d["xbar"][0] - 1e-4:
        continue
    a_true, ared_t, s_red, Jvec = reduced(d, d["lam"])
    check(abs(xt[0] - a_true) < 2e-4, f"part 2: true holding differs from the closed form, instance {it}")
    g = d["gamma"]
    m_true = ared_t - g * s_red * d["xm"][0]
    held = -d["km"][0] <= m_true <= d["kp"][0]
    for k in range(4):
        e = rng.normal(0, 0.006, d["K"])
        xh, _ = solve_joint(d, d["lam"] + e)
        if not interior_etfs(d, xh) or xh[0] > d["xbar"][0] - 1e-4:
            continue
        a_hat, ared_h, _, _ = reduced(d, d["lam"] + e)
        check(abs(xh[0] - a_hat) < 2e-4, f"part 2: perturbed holding differs from the closed form, instance {it}")
        leak = float(Jvec @ e)
        check(abs(ared_h - ared_t - leak) < 1e-12, "part 2a: the reduced alpha shift is not B^A J' e")
        check(abs(a_hat - a_true) <= abs(leak) / (g * s_red) + 1e-9, f"part 2b: move exceeds |B^A J' e|/(gamma s^red), instance {it}")
        if held:
            slack_up = d["kp"][0] - m_true; slack_dn = m_true + d["km"][0]
            flipped = abs(a_hat - d["xm"][0]) > 1e-6
            predicted = (leak > slack_up + 1e-12) or (leak < -slack_dn - 1e-12)
            if abs(leak - slack_up) > 1e-6 and abs(leak + slack_dn) > 1e-6:
                check(flipped == predicted, f"part 2c: flip test disagrees (leak {leak:.5f}, slack up {slack_up:.5f}, down {slack_dn:.5f}), instance {it}")
                counts["p2flip"] += 1
        # 2d: loss in the true reduced objective from holding a_hat instead of a_true
        def psi(a):
            return ared_t * a - 0.5 * g * s_red * a * a - d["kp"][0] * max(a - d["xm"][0], 0) - d["km"][0] * max(d["xm"][0] - a, 0)
        loss = psi(a_true) - psi(a_hat)
        mJ = ared_t - g * s_red * a_true; mu = max(0.0, mJ - d["kp"][0], -d["km"][0] - mJ)
        dl = abs(a_hat - a_true)
        check(-1e-12 <= loss <= 0.5 * g * s_red * dl * dl + (d["kp"][0] + d["km"][0] + mu) * dl + 1e-12, f"part 2d: loss bracket fails, instance {it}")
        # the same loss measured by the solver at the true premium with the fund fixed at a_hat, ETFs re-optimized
        xf, Jf = solve_joint(d, d["lam"], fix_funds=np.concatenate([[a_hat], xt[1:d["N"]]]))
        if interior_etfs(d, xf):   # outside the hypothesis when pinning the fund drives the ETF to a bound
            check(abs((Jt - Jf) - loss) < 3e-6, f"part 2d: solver loss {Jt - Jf:.3e} differs from psi loss {loss:.3e}, instance {it}")
        counts["p2"] += 1

# (iii) spanning: the naive rule's loss formula
for it in range(200):
    d = instance(3, 2, 2)
    d["xm"][:d["N"]] = rng.uniform(0.0, 0.2, d["N"])   # small incumbents keep the naive re-hedge feasible
    xJ, J = solve_joint(d, d["lam"])
    if not interior_etfs(d, xJ):
        continue
    g = d["gamma"]; N = d["N"]
    mu_hat = d["alpha"] + d["BA"] @ d["lam"]
    sig2 = d["v"] + np.einsum("ik,kl,il->i", d["BA"], d["Sft"], d["BA"])
    a_naive = np.clip(np.clip(d["xm"][:N], (mu_hat - d["kp"][:N]) / (g * sig2), (mu_hat + d["km"][:N]) / (g * sig2)), 0.0, d["xbar"][:N])
    a_hedged = np.clip(np.clip(d["xm"][:N], (d["alpha"] - d["kp"][:N]) / (g * d["v"]), (d["alpha"] + d["km"][:N]) / (g * d["v"])), 0.0, d["xbar"][:N])
    check(np.max(np.abs(xJ[:N] - a_hedged)) < 2e-4, f"part 3: joint holdings differ from the alpha band, instance {it}")
    def psi_i(i, a):
        return d["alpha"][i] * a - 0.5 * g * d["v"][i] * a * a - d["kp"][i] * max(a - d["xm"][i], 0) - d["km"][i] * max(d["xm"][i] - a, 0)
    formula = sum(psi_i(i, a_hedged[i]) - psi_i(i, a_naive[i]) for i in range(N))
    xn, Jn = solve_joint(d, d["lam"], fix_funds=a_naive)
    if not interior_etfs(d, xn):
        continue
    check(abs((J - Jn) - formula) < 3e-6, f"part 3: naive loss {J - Jn:.3e} differs from the formula {formula:.3e}, instance {it}")
    check(formula >= -1e-12, "part 3: negative naive loss")
    counts["p3"] += 1

print("cases:", counts)
check(counts["p1"] >= 10 and counts["p2"] >= 20 and counts["p2flip"] >= 5 and counts["p3"] >= 10, "too few instances exercised a part")
if FAIL:
    print(f"{len(FAIL)} check(s) failed"); sys.exit(1)
print("all checks passed")
