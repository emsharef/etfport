"""Solver checks of claim 048 (D23: many funds and many ETFs over two reviews; the two-number structure and spanning
separation at the root); not its proof.

Run: uv run python checks/048/check.py

A general joint two-review solver (cvxpy/CLARABEL) for N funds and M ETFs with a funded budget; checks:
 (i)   part 1: at the dynamic optimum every instrument's root line holds with the one dynamic cash price and its own
       incumbent value (tomorrow's slopes pinned by tomorrow's lines), for N = 2 funds and M = 2 ETFs;
 (ii)  part 2: with spanning frictionless ETFs today, the dynamic root's total exposure is the frictionless target at the
       tilted premium lambda_hat + R S_E, and each fund's root holding is its one-fund clip with the residual alpha
       alpha_hat_i + S_{A,i} - r_i' S_E and its residual variance (the separation);
 (iii) part 4: with costly ETFs today the separation fails (counted, not asserted).
Random assumed inputs (rule 22). Floating point, not a certificate.
"""
import sys

import cvxpy as cp
import numpy as np

rng = np.random.default_rng(48)
FAIL = []
TOL = 5e-4


def check(cond, msg):
    if not cond:
        FAIL.append(msg); print("FAIL:", msg)


def instance(N=2, M=2, frictionless=True, tight=True, S=3):
    K = M
    BA = rng.uniform(0.3, 1.2, (N, K)); BE = rng.uniform(0.5, 1.5, (M, K)) * (0.7 * np.eye(M) + 0.3)
    Sf = np.diag(rng.uniform(0.003, 0.01, K)); Pl = np.diag(rng.uniform(0.0, 0.0005, K)); Sft = Sf + Pl
    v = rng.uniform(0.001, 0.004, N)
    lam = rng.uniform(0.0, 0.03, K); alpha = rng.uniform(-0.005, 0.03, N)
    kpA, kmA = rng.uniform(0.005, 0.03, N), rng.uniform(0.005, 0.03, N)
    kpE = np.zeros(M) if frictionless else rng.uniform(0.001, 0.004, M); kmE = np.zeros(M) if frictionless else rng.uniform(0.001, 0.004, M)
    gamma = rng.uniform(2.0, 6.0); B = np.vstack([BA, BE]); n = N + M
    Sig0 = B @ Sft @ B.T + np.diag(np.concatenate([v, np.zeros(M)]))
    mu0 = np.concatenate([alpha + BA @ lam, BE @ lam])
    d = dict(N=N, M=M, K=K, n=n, BA=BA, BE=BE, Sft=Sft, v=v, lam=lam, alpha=alpha, gamma=gamma, beta=0.98,
             kp=np.concatenate([kpA, kpE]), km=np.concatenate([kmA, kmE]), xbar=np.concatenate([np.full(N, 1.2), np.full(M, 8.0)]),
             mu0=mu0, Sig0=Sig0, xm0=np.concatenate([rng.uniform(0.0, 0.3, N), rng.uniform(0.0, 0.5, M)]),
             h0=rng.uniform(0.05, 0.3) if tight else 50.0, q=np.full(S, 1.0 / S), mu1=[], Sig1=[], g=[])
    for _ in range(S):
        el = rng.normal(scale=0.006, size=K); ea = rng.normal(scale=0.008, size=N)
        d["mu1"].append(np.concatenate([alpha + ea + BA @ (lam + el), BE @ (lam + el)]))
        d["Sig1"].append(B @ (Sf + 0.7 * Pl) @ B.T + np.diag(np.concatenate([v * 0.9, np.zeros(M)])))
        d["g"].append(1.0 + np.concatenate([rng.uniform(-0.1, 0.15, N), rng.uniform(-0.08, 0.1, M)]))
    return d


def cost_expr(u, kp, km):
    return cp.sum(cp.multiply(kp, cp.pos(u)) + cp.multiply(km, cp.pos(-u)))


def solve_dynamic(d):
    n, S = d["n"], len(d["q"]); x0 = cp.Variable(n); x1 = [cp.Variable(n) for _ in range(S)]
    u0 = x0 - d["xm0"]; h0p = d["h0"] - cp.sum(u0) - cost_expr(u0, d["kp"], d["km"])
    obj = d["mu0"] @ x0 - 0.5 * d["gamma"] * cp.quad_form(x0, cp.psd_wrap(d["Sig0"])) - cost_expr(u0, d["kp"], d["km"])
    cons = [x0 >= 0, x0 <= d["xbar"]]; c0 = h0p >= 0; cons.append(c0); c1 = []
    for z in range(S):
        u1 = x1[z] - cp.multiply(d["g"][z], x0); h1p = h0p - cp.sum(u1) - cost_expr(u1, d["kp"], d["km"])
        obj = obj + d["beta"] * d["q"][z] * (d["mu1"][z] @ x1[z] - 0.5 * d["gamma"] * cp.quad_form(x1[z], cp.psd_wrap(d["Sig1"][z])) - cost_expr(u1, d["kp"], d["km"]))
        cz = h1p >= 0; c1.append(cz); cons += [x1[z] >= 0, x1[z] <= d["xbar"], cz]
    p = cp.Problem(cp.Maximize(obj), cons); p.solve(solver=cp.CLARABEL)
    eta0 = float(c0.dual_value); eta1 = [float(cz.dual_value) / (d["beta"] * d["q"][z]) for z, cz in enumerate(c1)]
    return np.array(x0.value).ravel(), [np.array(v_.value).ravel() for v_ in x1], eta0, eta1


def slopes_tomorrow_full(d, z, x1, x0, eta1):
    xm1 = d["g"][z] * x0; g1 = d["mu1"][z] - d["gamma"] * d["Sig1"][z] @ x1; eps = 1e-4
    lo = np.zeros(d["n"]); hi = np.zeros(d["n"])
    for i in range(d["n"]):
        kp, km = d["kp"][i], d["km"][i]; t_int = (g1[i] - eta1) / (1 + eta1)
        if x1[i] > xm1[i] + eps: lo[i] = hi[i] = kp
        elif x1[i] < xm1[i] - eps: lo[i] = hi[i] = -km
        elif x1[i] < eps: lo[i], hi[i] = max(-km, t_int), kp
        elif x1[i] > d["xbar"][i] - eps: lo[i], hi[i] = -km, min(kp, t_int)
        else: lo[i] = hi[i] = min(max(t_int, -km), kp)
    return lo, hi


def incumbent_values(d, x0, x1, eta1):
    Slo = np.zeros(d["n"]); Shi = np.zeros(d["n"])
    for z in range(len(d["q"])):
        lo, hi = slopes_tomorrow_full(d, z, x1[z], x0, eta1[z])
        Slo += d["beta"] * d["q"][z] * d["g"][z] * (eta1[z] + (1 + eta1[z]) * lo); Shi += d["beta"] * d["q"][z] * d["g"][z] * (eta1[z] + (1 + eta1[z]) * hi)
    return Slo, Shi


def root_lines_ok(d, x0, x1, eta0, eta1):
    g0 = d["mu0"] - d["gamma"] * d["Sig0"] @ x0
    eta_hat = eta0 + d["beta"] * sum(d["q"][z] * eta1[z] for z in range(len(d["q"])))
    Slo, Shi = incumbent_values(d, x0, x1, eta1); eps = 1e-4; ok = True
    for i in range(d["n"]):
        kp, km = d["kp"][i], d["km"][i]
        lo0 = kp if x0[i] > d["xm0"][i] + eps else (-km if x0[i] < d["xm0"][i] - eps else -km)
        hi0 = kp if x0[i] > d["xm0"][i] + eps else (-km if x0[i] < d["xm0"][i] - eps else kp)
        r_lo = g0[i] + Slo[i] - eta_hat - (1 + eta_hat) * hi0; r_hi = g0[i] + Shi[i] - eta_hat - (1 + eta_hat) * lo0
        if x0[i] < eps: ok &= r_lo <= TOL
        elif x0[i] > d["xbar"][i] - eps: ok &= r_hi >= -TOL
        else: ok &= (r_lo <= TOL) and (r_hi >= -TOL)
    return ok, eta_hat, (Slo, Shi)


def part_i():
    n_bind = 0
    for _ in range(40):
        d = instance(frictionless=bool(rng.integers(2)), tight=True)
        x0, x1, eta0, eta1 = solve_dynamic(d)
        ok, eta_hat, _ = root_lines_ok(d, x0, x1, eta0, eta1)
        check(ok, "part 1: a root line fails with the one cash price and the instrument's incumbent value")
        n_bind += int(max(eta1) > 1e-6)
    print(f"  part 1: root lines with one dynamic cash price and per-instrument incumbent values hold at 40 optima (N = 2, M = 2; {n_bind} with a binding state tomorrow)")


def part_ii_iii():
    n_sep = n_tested = 0; n_cost_fail = n_cost = 0
    for _ in range(240):
        frictionless = bool(rng.integers(2))
        d = instance(frictionless=frictionless, tight=True)
        d["h0"] = float(rng.uniform(0.2, 0.6))   # slack today likely, tomorrow may bind
        x0, x1, eta0, eta1 = solve_dynamic(d)
        if eta0 > 1e-6: continue
        N, M = d["N"], d["M"]
        if np.any(x0[N:] < 1e-3) or np.any(x0[N:] > d["xbar"][N:] - 1e-3): continue   # ETFs interior
        ok, eta_hat, (Slo, Shi) = root_lines_ok(d, x0, x1, eta0, eta1)
        if np.any(Shi - Slo > 1e-9): continue                                          # incumbent values pinned
        S = Slo; SE = S[N:]; SA = S[:N]
        R = np.linalg.inv(d["BE"]); one = np.ones(M)
        lam_res = d["lam"] + R @ (SE - eta_hat * one)                                     # the reserve tilt net of the cash price
        b_target = np.linalg.solve(d["gamma"] * d["Sft"], lam_res); b0 = np.vstack([d["BA"], d["BE"]]).T @ x0
        r = (R.T @ d["BA"].T)                                                             # columns r_i
        alpha_res = d["alpha"] + SA - r.T @ SE - eta_hat * (1 - r.T @ one)               # net cash of a unit netted through the ETFs
        clip = np.array([min(max(d["xm0"][i], (alpha_res[i] - (1 + eta_hat) * d["kp"][i]) / (d["gamma"] * d["v"][i])), (alpha_res[i] + (1 + eta_hat) * d["km"][i]) / (d["gamma"] * d["v"][i])) for i in range(N)])
        clip = np.clip(clip, 0, d["xbar"][:N])
        sep = np.allclose(b0, b_target, atol=2e-3) and np.allclose(x0[:N], clip, atol=2e-3)
        if frictionless:
            n_tested += 1; n_sep += int(sep)
            check(sep, f"part 2: separation fails with frictionless spanning ETFs (exposure gap {np.abs(b0 - b_target).max():.2e}, fund gap {np.abs(x0[:N] - clip).max():.2e})")
        else:
            n_cost += 1; n_cost_fail += int(not sep)
    print(f"  part 2: with spanning frictionless ETFs the dynamic root's exposure is the tilted frictionless target and the funds are their residual clips in {n_sep} of {n_tested}; "
          f"with costly ETFs the separation fails in {n_cost_fail} of {n_cost} (counted only)")


def main():
    part_i(); part_ii_iii()
    if FAIL:
        print(f"checks/048: {len(FAIL)} failure(s)"); sys.exit(1)
    print("checks/048: all checks passed")


if __name__ == "__main__":
    main()
