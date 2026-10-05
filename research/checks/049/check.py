"""Solver checks of claim 049 (D25: the quantile flexibility test for the full menu and the loss bound of repeated one-review
optimization with bands); not its proof.

Run: uv run python checks/049/check.py

Reuses checks/048/check.py's instances (N funds, M ETFs, two reviews, funded budget) and joint solver. Checks:
 (i)   part 1: in a state where the liquid reserve liq(z') (cash plus the ETFs' sale proceeds down to their solo sale
       thresholds) covers the need (the instruments' solo-target purchases), tomorrow's budget is slack: the relaxed
       optimum is fundable and the budgeted solve's multiplier is zero;
 (ii)  part 3: the myopic policy's loss against the dynamic optimum is at most the band term (1/2) S'(gamma Sigma_0)^{-1} S
       (S the incumbent values at the myopic root's relaxed tomorrow) plus beta E[eta_bar D] (D the shortfall), and at most
       the same bound with the band term in the inputs;
 (iii) part 2: the tail term equals the fraction of uncovered states times the Rockafellar-Uryasev tail measure of eta_bar D
       at that level, and a cash sweep illustrates the test (rule 22).
Random assumed inputs (rule 22). Floating point, not a certificate.
"""
import importlib.util
import os
import sys

import cvxpy as cp
import numpy as np


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(os.path.dirname(__file__), "..", rel, "check.py"))
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod


c48 = _load("check048", "048")
rng = np.random.default_rng(49)
c48.rng = rng
FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg); print("FAIL:", msg)


def cost_np(u, kp, km):
    return float((kp * np.maximum(u, 0) + km * np.maximum(-u, 0)).sum())


def myopic_root(d):
    """today's one-review optimum (the repeated one-review policy's root)."""
    x0 = cp.Variable(d["n"]); u0 = x0 - d["xm0"]; h0p = d["h0"] - cp.sum(u0) - c48.cost_expr(u0, d["kp"], d["km"])
    obj = d["mu0"] @ x0 - 0.5 * d["gamma"] * cp.quad_form(x0, cp.psd_wrap(d["Sig0"])) - c48.cost_expr(u0, d["kp"], d["km"])
    c0 = h0p >= 0; p = cp.Problem(cp.Maximize(obj), [x0 >= 0, x0 <= d["xbar"], c0]); p.solve(solver=cp.CLARABEL)
    return np.array(x0.value).ravel(), float(c0.dual_value)


def f0(d, x0):
    u0 = x0 - d["xm0"]
    return float(d["mu0"] @ x0 - 0.5 * d["gamma"] * x0 @ d["Sig0"] @ x0) - cost_np(u0, d["kp"], d["km"])


def cash_today(d, x0):
    u0 = x0 - d["xm0"]; return float(d["h0"] - u0.sum() - cost_np(u0, d["kp"], d["km"]))


def solve_tomorrow(d, z, x0, h, budget=True):
    """tomorrow's one-review optimum at state z from the marked holdings and cash h; returns holdings, value, multiplier, cash used."""
    x1 = cp.Variable(d["n"]); xm1 = d["g"][z] * x0; u1 = x1 - xm1
    used = cp.sum(u1) + c48.cost_expr(u1, d["kp"], d["km"])
    obj = d["mu1"][z] @ x1 - 0.5 * d["gamma"] * cp.quad_form(x1, cp.psd_wrap(d["Sig1"][z])) - c48.cost_expr(u1, d["kp"], d["km"])
    cons = [x1 >= 0, x1 <= d["xbar"]]; cz = None
    if budget:
        cz = used <= h; cons.append(cz)
    p = cp.Problem(cp.Maximize(obj), cons); p.solve(solver=cp.CLARABEL)
    x1v = np.array(x1.value).ravel(); u = x1v - xm1
    return x1v, float(p.value), (float(cz.dual_value) if budget else 0.0), float(u.sum() + cost_np(u, d["kp"], d["km"]))


def J(d, x0, budget=True):
    """the joint objective of holding x0 today and optimizing tomorrow (with or without tomorrow's budget)."""
    h = cash_today(d, x0); val = f0(d, x0); out = []
    for z in range(len(d["q"])):
        x1, w, eta, used = solve_tomorrow(d, z, x0, h, budget); val += d["beta"] * d["q"][z] * w; out.append((x1, w, eta, used))
    return val, out


def need_liq(d, z, x0, h):
    """claim 113's objects over the full menu: solo targets, the need, the ETFs' solo sale thresholds, the liquid reserve."""
    N = d["N"]; mu, Sig, g = d["mu1"][z], d["Sig1"][z], d["g"][z]
    xhat = np.maximum(mu - d["kp"], 0) / (d["gamma"] * np.diag(Sig))
    need = float(((1 + d["kp"]) * np.maximum(xhat - g * x0, 0)).sum())
    xcheck = (mu[N:] + d["km"][N:]) / (d["gamma"] * np.diag(Sig)[N:])
    liq = h + float(((1 - d["km"][N:]) * np.maximum(g[N:] * x0[N:] - np.maximum(xcheck, 0), 0)).sum())
    return need, liq


def eta_bar(d, z):
    return float(np.max(np.maximum(d["mu1"][z] - d["kp"], 0) / (1 + d["kp"])))


def tail_measure(y, q, eps):
    """Rockafellar-Uryasev's F at level 1 - eps minimized over c: min_c c + E(y - c)^+ / eps, on a finite law (c over the atoms and 0)."""
    cands = np.concatenate([[0.0], y])
    return float(min(c + float((q * np.maximum(y - c, 0)).sum()) / eps for c in cands))


def part_i():
    n_cov = n_states = 0
    for _ in range(60):
        d = c48.instance(frictionless=bool(rng.integers(2)), tight=True)
        d["h0"] = float(rng.uniform(0.05, 3.0))
        for x0 in (myopic_root(d)[0], c48.solve_dynamic(d)[0]):
            h = cash_today(d, x0)
            for z in range(len(d["q"])):
                n_states += 1
                need, liq = need_liq(d, z, x0, h)
                if liq >= need - 1e-9:
                    n_cov += 1
                    x1r, wr, _, used_r = solve_tomorrow(d, z, x0, h, budget=False)
                    check(used_r <= h + 1e-6, f"part 1: covered state (liq {liq:.4f} >= need {need:.4f}) yet the relaxed optimum uses {used_r:.4f} > cash {h:.4f}")
                    x1b, wb, eta, _ = solve_tomorrow(d, z, x0, h, budget=True)
                    check(abs(wb - wr) < 1e-7 and eta < 1e-3, f"part 1: covered state yet tomorrow's budget binds (eta {eta:.2e}, value gap {wr - wb:.2e})")
    print(f"  part 1: in {n_cov} covered states (of {n_states}, at myopic and dynamic roots) the relaxed optimum is fundable and the budget is slack")


def part_ii_iii():
    n = n_unc = 0; ratios = []; eps_seen = []
    for _ in range(80):
        d = c48.instance(frictionless=bool(rng.integers(2)), tight=True)
        d["h0"] = float(rng.uniform(0.02, 3.0))
        x0d, x1d, eta0d, eta1d = c48.solve_dynamic(d)
        Jd, _ = J(d, x0d, budget=True)
        x0m, _ = myopic_root(d); Jm, out_m = J(d, x0m, budget=True); Jm_s, out_s = J(d, x0m, budget=False)
        loss = Jd - Jm
        # the band term: S at the myopic root's relaxed tomorrow, slopes pinned by the regimes with eta = 0
        S = np.zeros(d["n"])
        for z in range(len(d["q"])):
            lo, hi = c48.slopes_tomorrow_full(d, z, out_s[z][0], x0m, 0.0); S += d["beta"] * d["q"][z] * d["g"][z] * lo
        band = 0.5 * S @ np.linalg.solve(d["gamma"] * d["Sig0"], S)
        b = d["beta"] * np.array([sum(d["q"][z] * d["g"][z][i] for z in range(len(d["q"]))) for i in range(d["n"])]) * np.maximum(d["kp"], d["km"])
        band_inputs = 0.5 * float(b @ b) * float(np.linalg.norm(np.linalg.inv(d["gamma"] * d["Sig0"]), 2))
        # the tail term: eta_bar times the shortfall, per state, at the myopic root
        h = cash_today(d, x0m); D = np.zeros(len(d["q"])); eb = np.zeros(len(d["q"])); relax_gap = 0.0
        for z in range(len(d["q"])):
            need, liq = need_liq(d, z, x0m, h); D[z] = max(need - liq, 0.0); eb[z] = eta_bar(d, z)
            relax_gap += d["beta"] * d["q"][z] * (out_s[z][1] - out_m[z][1])
            check(out_s[z][1] - out_m[z][1] <= eb[z] * D[z] + 1e-7, f"part 3: a state's relaxation gap {out_s[z][1] - out_m[z][1]:.3e} exceeds eta_bar D = {eb[z] * D[z]:.3e}")
        tail = d["beta"] * float((d["q"] * eb * D).sum())
        n += 1; n_unc += int(D.max() > 0)
        check(loss <= band + tail + 1e-6, f"part 3: loss {loss:.3e} exceeds band {band:.3e} + tail {tail:.3e}")
        check(band <= band_inputs + 1e-12, "part 3: the band term exceeds its input bound")
        if band + tail > 1e-9: ratios.append(loss / (band + tail))
        # part 2: the tail term is the uncovered fraction times the tail measure at that level
        eps = float((d["q"] * (D > 0)).sum())
        if 0 < eps < 1:
            y = eb * D; tm = tail_measure(y, d["q"], eps); ey = float((d["q"] * y).sum())
            check(abs(ey - eps * tm) <= 1e-9 * max(1.0, ey), f"part 2: E[eta_bar D] = {ey:.3e} but eps * tail measure = {eps * tm:.3e}")
            eps_seen.append(eps)
    print(f"  part 3: the loss of repeated one-review optimization is within the band-plus-tail bound at {n} instances ({n_unc} with an uncovered state); "
          f"loss over bound: median {np.median(ratios):.3f}, max {np.max(ratios):.3f}")
    print(f"  part 2: E[eta_bar D] = eps x (the tail measure at level 1 - eps) in {len(eps_seen)} instances with 0 < eps < 1")


def sweep():
    """illustration: today's cash swept; the uncovered fraction, the bound and the loss (rule 22, tested cells only)."""
    d = c48.instance(N=2, M=2, frictionless=False, tight=True, S=6)
    print("  cash sweep (one instance, N = 2, M = 2, 6 states): cash, uncovered fraction eps, loss bp, band term bp, tail term bp")
    for h0 in (0.05, 0.2, 0.5, 1.0, 2.0, 4.0):
        d["h0"] = h0
        x0d, *_ = c48.solve_dynamic(d); Jd, _ = J(d, x0d); x0m, _ = myopic_root(d); Jm, out_m = J(d, x0m); Jm_s, out_s = J(d, x0m, budget=False)
        S = np.zeros(d["n"])
        for z in range(len(d["q"])):
            lo, _ = c48.slopes_tomorrow_full(d, z, out_s[z][0], x0m, 0.0); S += d["beta"] * d["q"][z] * d["g"][z] * lo
        band = 0.5 * S @ np.linalg.solve(d["gamma"] * d["Sig0"], S); h = cash_today(d, x0m)
        D = np.array([max(np.subtract(*need_liq(d, z, x0m, h)), 0.0) for z in range(len(d["q"]))]); eb = np.array([eta_bar(d, z) for z in range(len(d["q"]))])
        eps = float((d["q"] * (D > 0)).sum()); tail = d["beta"] * float((d["q"] * eb * D).sum())
        print(f"    {h0:.2f}  {eps:.2f}  {1e4 * (Jd - Jm):.3f}  {1e4 * band:.3f}  {1e4 * tail:.3f}")


def main():
    part_i(); part_ii_iii(); sweep()
    if FAIL:
        print(f"checks/049: {len(FAIL)} failure(s)"); sys.exit(1)
    print("checks/049: all checks passed")


if __name__ == "__main__":
    main()
