"""Solver checks of claim 046 (D16 second claim, the refile of refuted 045: bounds in the inputs for the two channels; the comparative static); not its proof.

Run: uv run python checks/046/check.py

Reuses checks/044/check.py's instances and joint solver. Checks:
 (i)   part 1: tomorrow's cash price admits an admissible value at most eta_bar(z') = max_i (mu_{1,i} - kappa^+_i)^+/(1 + kappa^+_i)
       (Sigma_AE >= 0), read at the solver's multiplier when a state buys and at the held lines' lower end otherwise;
 (ii)  part 1: the slack-tomorrow sufficient condition (cash at least the solo-target purchases) implies eta_1 = 0;
 (iii) part 2: S_i >= -beta E[g_i] kappa^-_i always, and the residual lies in its bracket;
 (iv)  part 3: with a frictionless interior ETF at both roots, the fund's dynamic holding minus the myopic one has the
       sign of the residual (the proved comparative static); with a costly ETF the naive reading is counted, not asserted.
Random assumed inputs (rule 22). Floating point, not a certificate.
"""
import importlib.util
import os
import sys

import numpy as np


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(os.path.dirname(__file__), "..", rel, "check.py"))
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod


c44 = _load("check044", "044")
rng = np.random.default_rng(45)
c44.rng = rng
FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg); print("FAIL:", msg)


def eta_bar(d, z):
    return max(max(d["mu1"][z][i] - d["kp"][i], 0.0) / (1 + d["kp"][i]) for i in range(2))


def admissible_eta_lower_end(d, z, x1, xm1, g1):
    """the smallest admissible cash price tomorrow from the lines at x1: bought interior pins it; else the held lines' lower end."""
    lo = 0.0
    for i in range(2):
        if x1[i] > xm1[i] + 1e-4 and x1[i] < d["xbar"][i] - 1e-4:
            return (g1[i] - d["kp"][i]) / (1 + d["kp"][i])
    for i in range(2):
        if abs(x1[i] - xm1[i]) <= 1e-4 and x1[i] < d["xbar"][i] - 1e-4:   # held below the cap: g <= eta + (1 + eta) kp
            lo = max(lo, (g1[i] - d["kp"][i]) / (1 + d["kp"][i]))
        if x1[i] > xm1[i] + 1e-4:                                           # bought to the cap: g >= eta + (1 + eta) kp gives an upper end only
            pass
    return lo


def part_i_ii():
    n_bind = n_slack_by_cond = 0
    for _ in range(60):
        d = c44.instance(tight=bool(rng.integers(2)))
        x0, x1, eta0, eta1, _ = c44.solve_dynamic(d)
        u0 = x0 - d["xm0"]; h0p = d["h0"] - u0.sum() - (d["kp"] * np.maximum(u0, 0) + d["km"] * np.maximum(-u0, 0)).sum()
        for z in range(len(d["q"])):
            g1 = d["mu1"][z] - d["gamma"] * d["Sig1"][z] @ x1[z]; xm1 = d["g"][z] * x0
            eb = eta_bar(d, z)
            if eta1[z] > 1e-6:
                n_bind += 1
                lo = admissible_eta_lower_end(d, z, x1[z], xm1, g1)
                check(lo <= eb + 1e-6, f"part 1: admissible cash price lower end {lo:.4f} exceeds eta_bar {eb:.4f}")
            # slack-tomorrow sufficient condition: cash >= sum (1 + kp)(x_hat - g x0)^+, x_hat = (mu - kp)^+/(gamma Sigma_ii)
            need = sum((1 + d["kp"][i]) * max(max(d["mu1"][z][i] - d["kp"][i], 0) / (d["gamma"] * d["Sig1"][z][i, i]) - xm1[i], 0) for i in range(2))
            if h0p >= need - 1e-9:
                n_slack_by_cond += 1; check(eta1[z] < 1e-5, f"part 1: slack condition holds (cash {h0p:.4f} >= need {need:.4f}) yet eta_1 = {eta1[z]:.3e}")
    print(f"  part 1: an admissible cash price at most eta_bar in {n_bind} binding states; the slack-tomorrow condition implied eta_1 = 0 in {n_slack_by_cond} states")


def part_iii():
    for _ in range(60):
        d = c44.instance(tight=True)
        x0, x1, eta0, eta1, _ = c44.solve_dynamic(d)
        ok, eta_hat, (Slo, Shi) = c44.root_lines_ok(d, x0, x1, eta0, eta1)
        for i in range(2):
            lb = -d["beta"] * sum(d["q"][z] * d["g"][z][i] for z in range(len(d["q"]))) * d["km"][i]
            check(Slo[i] >= lb - 1e-9, f"part 2: S_i lower end {Slo[i]:.3e} below -beta E[g_i] kappa^-_i = {lb:.3e}")
            Ee = sum(d["q"][z] * eta1[z] for z in range(len(d["q"])))
            ub = d["beta"] * sum(d["q"][z] * d["g"][z][i] * (eta1[z] + (1 + eta1[z]) * d["kp"][i]) for z in range(len(d["q"])))
            check(Shi[i] <= ub + 1e-9, "part 2: S_i upper end above its bracket")
    print("  part 2: the incumbent values respect the input bracket on 60 tight instances (lower end never below claim 029's, whatever the budget)")


def solve_fix_a(d, a):
    """the joint program with the fund's root holding fixed at a: the ETF re-optimized dynamically given a."""
    import cvxpy as cp
    S = len(d["q"]); x0 = cp.Variable(2); x1 = [cp.Variable(2) for _ in range(S)]
    u0 = x0 - d["xm0"]; h0p = d["h0"] - cp.sum(u0) - c44.cost_expr(u0, d["kp"], d["km"])
    obj = c44.score(d["mu0"], d["Sig0"], x0, d["gamma"]) - c44.cost_expr(u0, d["kp"], d["km"])
    cons = [x0 >= 0, x0 <= d["xbar"], x0[0] == a]; c0 = h0p >= 0; cons.append(c0); c1 = []
    for z in range(S):
        u1 = x1[z] - cp.multiply(d["g"][z], x0); h1p = h0p - cp.sum(u1) - c44.cost_expr(u1, d["kp"], d["km"])
        obj = obj + d["beta"] * d["q"][z] * (c44.score(d["mu1"][z], d["Sig1"][z], x1[z], d["gamma"]) - c44.cost_expr(u1, d["kp"], d["km"]))
        cz = h1p >= 0; c1.append(cz); cons += [x1[z] >= 0, x1[z] <= d["xbar"], cz]
    p = cp.Problem(cp.Maximize(obj), cons); p.solve(solver=cp.CLARABEL)
    eta0 = float(c0.dual_value); eta1 = [float(cz.dual_value) / (d["beta"] * d["q"][z]) for z, cz in enumerate(c1)]
    return np.array(x0.value).ravel(), [np.array(v.value).ravel() for v in x1], eta0, eta1


def residual_fund(d, x0, x1, eta0, eta1, hedge=False):
    """the fund's residual bracket; with hedge=True, net of today's hedge ratio times the ETF's residual (frictionless ETF)."""
    ok, eta_hat, (Slo, Shi) = c44.root_lines_ok(d, x0, x1, eta0, eta1)
    Ee = sum(d["q"][z] * eta1[z] for z in range(len(d["q"])))
    lo = Slo[0] - d["beta"] * Ee * (1 + d["kp"][0]); hi = Shi[0] - d["beta"] * Ee * (1 + d["kp"][0])
    if hedge:
        rho0 = d["Sig0"][0, 1] / d["Sig0"][1, 1]; rE_lo = Slo[1] - d["beta"] * Ee; rE_hi = Shi[1] - d["beta"] * Ee
        lo, hi = lo - rho0 * max(rE_lo, rE_hi), hi - rho0 * min(rE_lo, rE_hi)
    return lo, hi


def part_iv():
    agree = total = 0; naive_agree = naive_total = 0
    for _ in range(400):
        free_etf = bool(rng.integers(2))
        d = c44.instance(tight=True)
        d["h0"] = float(rng.uniform(0.06, 0.25)); d["xm0"][0] = float(rng.uniform(0.0, 0.15))   # slack today, a purchase likely, tight tomorrow possible
        d["mu0"][0] += 0.02; d["mu1"] = [m + np.array([0.02, 0.0]) for m in d["mu1"]]
        if free_etf: d["kp"][1] = d["km"][1] = 0.0
        x0m, x1m, eta0m, eta1m = c44.myopic_policy(d)
        x0d, *_ = c44.solve_dynamic(d)
        u0 = x0m - d["xm0"]; h0p = d["h0"] - u0.sum() - (d["kp"] * np.maximum(u0, 0) + d["km"] * np.maximum(-u0, 0)).sum()
        if not (x0m[0] > d["xm0"][0] + 1e-3 and x0m[0] < d["xbar"][0] - 1e-3 and h0p > 1e-4): continue
        diff = x0d[0] - x0m[0]
        if abs(diff) < 1e-4: continue
        if free_etf:
            # the reduced residual: the ETF re-optimized dynamically at the myopic fund holding
            x0r, x1r, eta0r, eta1r = solve_fix_a(d, x0m[0])
            if not (x0r[1] > 1e-3 and x0d[1] > 1e-3): continue     # ETF interior at both
            u0r = x0r - d["xm0"]; h0pr = d["h0"] - u0r.sum() - (d["kp"] * np.maximum(u0r, 0) + d["km"] * np.maximum(-u0r, 0)).sum()
            if h0pr <= 1e-4: continue                              # today's budget slack at the reduced point too
            r_lo, r_hi = residual_fund(d, x0r, x1r, eta0r, eta1r, hedge=True)
            if r_lo <= 0 <= r_hi or abs(r_lo) < 1e-5: continue
            total += 1; agree += int(np.sign(diff) == np.sign(r_lo))
            check(np.sign(diff) == np.sign(r_lo), f"part 3: frictionless interior ETF yet the fund moved against the hedged reduced residual ({r_lo:.2e}, diff {diff:.2e})")
        else:
            r_lo, r_hi = residual_fund(d, x0m, x1m, eta0m, eta1m)   # the naive residual at the myopic pair
            if r_lo <= 0 <= r_hi or abs(r_lo) < 1e-5: continue
            naive_total += 1; naive_agree += int(np.sign(diff) == np.sign(r_lo))
    print(f"  part 3: with a frictionless interior ETF the fund's dynamic-minus-myopic holding has the sign of the reduced residual net of the hedge term in {agree} of {total}; "
          f"with a costly ETF the naive reading (the residual at the myopic pair) held in {naive_agree} of {naive_total} (counted only)")


def main():
    part_i_ii(); part_iii(); part_iv()
    if FAIL:
        print(f"checks/046: {len(FAIL)} failure(s)"); sys.exit(1)
    print("checks/046: all checks passed")


if __name__ == "__main__":
    main()
