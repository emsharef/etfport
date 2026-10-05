"""Solver checks of claim 041 (M7, one review: two-stage exactness when ETFs sit at their zero bound); not its proof.

Run: uv run python checks/041/check.py

 (i)   part 1: the fibre-confined procedure is exact iff stage 2's holdings satisfy claim 040's fund bands with the
       stage-1 slacks zeta* = gamma Sigma_EE w* - mu_E (both directions, random instances against cvxpy);
 (ii)  part 2 (one fund): the fibre interval stage 1 leaves for the fund, stage 2's clipped band solution, exactness
       iff x_J lies in the fibre interval (both directions), and the loss
       decomposition Lambda = [Phi(x_J) - Phi(x_2)] + [V_E(r x_2) - G_E(w*)];
 (iii) part 3: the soft procedure with an unconstrained stage 1 is exact with ETFs at zero; with R = B_F it is exact
       iff the factor Markowitz exposure is reachable (some fund holding's by-product lies below it coordinatewise).
Random assumed inputs (rule 22: illustrations). Floating point, not a certificate. Uses checks/040/check.py's instance,
joint solver and active-set exposure solver (fees off here, as in claim 104's split).
"""
import importlib.util
import os
import sys

import cvxpy as cp
import numpy as np


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(os.path.dirname(__file__), "..", rel, "check.py"))
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod


c40 = _load("check040", "040")
rng = np.random.default_rng(41)
c40.rng = rng
FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg); print("FAIL:", msg)


def G_E(d, w):
    return d["muE"] @ w - 0.5 * d["gamma"] * w @ d["SEE"] @ w


def H(d, xA, xmA):
    return d["at"] @ xA - 0.5 * d["gamma"] * xA @ np.diag(d["v"]) @ xA - np.sum(d["kp"] * np.maximum(xA - xmA, 0) + d["km"] * np.maximum(xmA - xA, 0))


def stage1(d):
    """max G_E(w) over W_F = {w >= Q x^A, x^A in the box}: the fibre-confined stage 1 in ETF coordinates."""
    N, M = d["N"], d["M"]
    w = cp.Variable(M); xA = cp.Variable(N)
    obj = d["muE"] @ w - 0.5 * d["gamma"] * cp.quad_form(w, cp.psd_wrap(d["SEE"]))
    p = cp.Problem(cp.Maximize(obj), [w >= d["Q"] @ xA, xA >= 0, xA <= d["xbarA"]]); p.solve(solver=cp.CLARABEL)
    return np.array(w.value).ravel(), p.value


def stage2(d, wstar, xmA):
    N = d["N"]
    xA = cp.Variable(N); u = xA - xmA
    cost = cp.sum(cp.multiply(d["kp"], cp.pos(u)) + cp.multiply(d["km"], cp.pos(-u)))
    obj = d["at"] @ xA - 0.5 * d["gamma"] * cp.quad_form(xA, cp.psd_wrap(np.diag(d["v"]))) - cost
    p = cp.Problem(cp.Maximize(obj), [d["Q"] @ xA <= wstar, xA >= 0, xA <= d["xbarA"]]); p.solve(solver=cp.CLARABEL)
    return np.array(xA.value).ravel(), p.value


def soft_stage2(d, wstar, xmA):
    """stage 2 of the soft procedure with target exposure w* (ETF coordinates): the joint problem with premia gamma Sigma_EE w*."""
    N, M = d["N"], d["M"]
    xA = cp.Variable(N); xE = cp.Variable(M); w = xE + d["Q"] @ xA; u = xA - xmA
    cost = cp.sum(cp.multiply(d["kp"], cp.pos(u)) + cp.multiply(d["km"], cp.pos(-u)))
    obj = d["at"] @ xA - 0.5 * d["gamma"] * cp.quad_form(xA, cp.psd_wrap(np.diag(d["v"]))) - cost \
        - 0.5 * d["gamma"] * cp.quad_form(w - wstar, cp.psd_wrap(d["SEE"]))
    p = cp.Problem(cp.Maximize(obj), [xE >= 0, xA >= 0, xA <= d["xbarA"]]); p.solve(solver=cp.CLARABEL)
    return np.array(xA.value).ravel(), np.array(xE.value).ravel()


def joint_value(d, x, xmA):
    N = d["N"]; w = x[N:] + d["Q"] @ x[:N]
    return G_E(d, w) + H(d, x[:N], xmA)


def part_i():
    n_exact = n_inexact = 0
    for _ in range(80):
        d = c40.instance(N=3, M=2, fees=False, lam_scale=float(rng.choice([0.5, 1.5])))
        N, M = d["N"], d["M"]; xmA = d["xm"][:N]
        xJ, J = c40.solve_joint(d); J = joint_value(d, xJ, xmA)
        wstar, _ = stage1(d); x2, _ = stage2(d, wstar, xmA); T = G_E(d, wstar) + H(d, x2, xmA)
        check(J - T >= -1e-7, "part 1: T exceeds J")
        zeta = d["gamma"] * d["SEE"] @ wstar - d["muE"]
        check(np.all(zeta >= -1e-6), "part 1: stage-1 slack negative (W_F is upward closed)")
        q2 = d["Q"] @ x2
        check(np.all(zeta * (wstar - q2) < 1e-4), "part 1: stage-1 slack positive where the fibre is slack at x_2")
        G = d["at"] - d["gamma"] * d["v"] * x2 - d["Q"].T @ zeta
        exact_by_bands = c40.band_ok(d, G, x2, xmA, tol=1e-4)   # a marginal off by 1e-4 costs about 1e-6 of value
        exact = (J - T) < 1e-6
        if exact: n_exact += 1
        else: n_inexact += 1
        if exact_by_bands and not exact: check(False, f"part 1: bands hold with zeta* at x_2 but J - T = {J - T:.2e}")
        if exact and not exact_by_bands:
            # a fund can sit off its band only within solver resolution
            off = max(max(G[i] - d["kp"][i], -d["km"][i] - G[i]) for i in range(N) if 1e-4 < x2[i] < d["xbarA"][i] - 1e-4) if np.any((x2 > 1e-4) & (x2 < d["xbarA"] - 1e-4)) else 0.0
            check(off < 2e-3, f"part 1: exact (J - T = {J - T:.1e}) but a fund is off its band by {off:.2e}")
    print(f"  part 1: fibre-confined exactness iff the bands hold with the stage-1 slacks, on 80 instances ({n_exact} exact, {n_inexact} inexact)")


def part_ii():
    n_exact = n_inexact = n_int = 0
    for _ in range(120):
        d = c40.instance(N=1, M=3, fees=False, lam_scale=float(rng.choice([0.5, 1.5])))
        if rng.integers(3) == 0:   # strong positive premia: the ETFs stay interior and the fibre leaves the fund room
            lam = rng.uniform(0.03, 0.08, 3); d["lam"] = lam; d["muE"] = d["BE"] @ lam
            d["mu"] = np.concatenate([d["alpha"] + d["BA"] @ lam, d["BE"] @ lam])
        d["xbarA"] = np.array([3.0]); xm = float(rng.uniform(0.0, 1.5)); d["xm"][0] = xm; xmA = np.array([xm])
        r = d["Q"][:, 0]
        xJ_full, _ = c40.solve_joint(d); xJ = xJ_full[0]; J = joint_value(d, xJ_full, xmA)
        wstar, _ = stage1(d)
        lo = max([0.0] + [wstar[j] / r[j] for j in range(3) if r[j] < -1e-12])
        hi = min([3.0] + [wstar[j] / r[j] for j in range(3) if r[j] > 1e-12])
        check(lo <= hi + 1e-7, "part 2: empty fibre interval")
        kp, km, g, v, a = d["kp"][0], d["km"][0], d["gamma"], d["v"][0], d["at"][0]
        xf = min(max(xm, (a - kp) / (g * v)), (a + km) / (g * v))
        x2_formula = min(max(xf, lo), hi)
        x2, _ = stage2(d, wstar, xmA)
        check(abs(x2[0] - x2_formula) < 2e-3, f"part 2: stage 2 {x2[0]:.4f} vs clipped band {x2_formula:.4f}")
        T = G_E(d, wstar) + H(d, x2, xmA)
        exact = (J - T) < 1e-7   # a displacement of 2e-3 costs about 1e-8
        if exact: n_exact += 1
        else: n_inexact += 1
        # iff: exact <=> x_J in the fibre interval (leanb's strengthening); strict interiors counted
        if lo + 1e-3 < xJ < hi - 1e-3:
            n_int += 1
        inside = lo - 2e-3 <= xJ <= hi + 2e-3
        if inside and not (lo - 2e-3 <= xJ <= lo + 2e-3 or hi - 2e-3 <= xJ <= hi + 2e-3):
            check(exact, f"part 2: x_J {xJ:.4f} inside [{lo:.4f}, {hi:.4f}] yet J - T = {J - T:.2e}")
        elif not inside:
            check(not exact, f"part 2: x_J {xJ:.4f} outside [{lo:.4f}, {hi:.4f}] yet exact")
        if exact: check(inside, "part 2: exact yet x_J outside the fibre interval")
        if exact: check(abs(x2[0] - xJ) < 1e-2, "part 2: exact yet x_2 far from x_J")
        else: check(abs(x2[0] - xJ) > 1e-3, "part 2: inexact yet x_2 = x_J")
        # loss decomposition
        VE2 = c40.V_E(d, r * x2[0])
        Phi = lambda x: H(d, np.array([x]), xmA) + c40.V_E(d, r * x)
        decomp = (Phi(xJ) - Phi(x2[0])) + (VE2 - G_E(d, wstar))
        check(abs((J - T) - decomp) < 1e-6, f"part 2: loss {J - T:.3e} vs Phi(x_J) - Phi(x_2) {decomp:.3e}")
        check(abs(VE2 - G_E(d, wstar)) < 1e-7, "part 2: the would-be exposure-misfit term is not zero")
    print(f"  part 2: one fund: fibre interval, clipped band, exactness iff x_J in the fibre interval, and the loss decomposition hold "
          f"on 120 instances ({n_exact} exact, {n_inexact} inexact; {n_int} with x_J strictly inside)")


def part_iii():
    n_reach = n_unreach = n_exact_nu = 0
    for _ in range(60):
        d = c40.instance(N=2, M=2, fees=False, lam_scale=float(rng.choice([0.5, 1.5])))
        N, M = d["N"], d["M"]; xmA = d["xm"][:N]
        xJ, _ = c40.solve_joint(d); J = joint_value(d, xJ, xmA)
        # unconstrained stage 1: w_TB
        wTB = np.linalg.solve(d["SEE"], d["muE"]) / d["gamma"]
        xA_s, xE_s = soft_stage2(d, wTB, xmA)
        Js = joint_value(d, np.concatenate([xA_s, xE_s]), xmA)
        check(abs(J - Js) < 2e-6, f"part 3: soft procedure with unconstrained stage 1 loses {J - Js:.2e}")
        # R = B_F: stage 1 over W_F; exact iff w_TB in W_F
        xA = cp.Variable(N); p = cp.Problem(cp.Minimize(0), [d["Q"] @ xA <= wTB, xA >= 0, xA <= d["xbarA"]]); p.solve(solver=cp.CLARABEL)
        reachable = p.status in ("optimal", "optimal_inaccurate")
        wstar, _ = stage1(d)
        xA_s2, xE_s2 = soft_stage2(d, wstar, xmA); Js2 = joint_value(d, np.concatenate([xA_s2, xE_s2]), xmA)
        if reachable:
            n_reach += 1; check(np.allclose(wstar, wTB, atol=1e-4) and abs(J - Js2) < 2e-6, "part 3: Markowitz exposure reachable yet the soft procedure over B_F is inexact")
        else:
            n_unreach += 1
            nu = d["muE"] - d["gamma"] * d["SEE"] @ wstar
            check(np.linalg.norm(nu) > 1e-6, "part 3: exposure unreachable yet the stage-1 multiplier vanishes")
            w2 = xE_s2 + d["Q"] @ xA_s2; wJ = xJ[N:] + d["Q"] @ xJ[:N]
            check(-1e-7 <= J - Js2 <= nu @ (wJ - w2) + 1e-7, f"part 3: soft loss {J - Js2:.2e} outside [0, nu'(w_J - w_2) = {nu @ (wJ - w2):.2e}]")
            if J - Js2 < 1e-7: n_exact_nu += 1
    print(f"  part 3: soft procedure exact with an unconstrained stage 1 on 60 instances; with R = B_F exact in the {n_reach} reachable cases; in the {n_unreach} unreachable the multiplier is nonzero, the bound with stage 2's exposure holds, and {n_exact_nu} are exact anyway")


def main():
    part_i(); part_ii(); part_iii()
    if FAIL:
        print(f"checks/041: {len(FAIL)} failure(s)"); sys.exit(1)
    print("checks/041: all checks passed")


if __name__ == "__main__":
    main()
