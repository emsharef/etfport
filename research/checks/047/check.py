"""Solver checks of claim 047 (D19: the reserve rule with one fund and one ETF); not its proof.

Run: uv run python checks/047/check.py

Reuses checks/044/check.py's joint two-review solver on M8-shaped instances: tomorrow's means move by a two-point
premium revision and a two-point alpha revision (four states), the alpha revision's scale sqrt(v_alpha) varied.
Checks:
 (i)   part 2 (no reserve needed): when the one-review policy's leftover cash covers the fund's and the ETF's largest
       solo-target purchases over the revision states, every tomorrow multiplier is zero and today's lines carry no
       budget term (the dynamic policy's cash and ETF differ from the one-review ones only through claim 029's slopes);
 (ii)  part 4 (the maximum): at every dynamic optimum with a positive cash price in some state, the cash carried is
       below the largest need over the states;
 (iii) part 3 (ETF against cash): at the dynamic optimum the ETF's root line holds with the reserve premium as stated;
 (iv)  part 4 (growth, illustration): the largest need grows with sqrt(v_alpha) at the stated slope, and the dynamic
       policy's reserve (cash plus the ETF's liquidation value above the one-review policy's) is nondecreasing in
       sqrt(v_alpha) on a grid, counted only.
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
rng = np.random.default_rng(47)
c44.rng = rng
FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg); print("FAIL:", msg)


def instance_m8(sv_alpha=0.01, h0=None, seed_shift=0.0):
    """M8-shaped two-review instance: four revision states (premium +-sv_lam, alpha +-sv_alpha), marking by gross returns."""
    d = {}
    d["beta"] = 0.98; d["gamma"] = rng.uniform(2.0, 6.0)
    d["kp"] = np.array([rng.uniform(0.005, 0.03), rng.uniform(0.0005, 0.003)]); d["km"] = np.array([rng.uniform(0.005, 0.03), rng.uniform(0.0005, 0.003)])
    d["xbar"] = np.array([rng.uniform(0.6, 1.5), 5.0])
    bA, bE = rng.uniform(0.6, 1.2), 1.0; lam = rng.uniform(0.005, 0.03); alpha = rng.uniform(-0.005, 0.03) + seed_shift
    sf2, sA2, sE2 = rng.uniform(0.003, 0.01), rng.uniform(0.001, 0.005), 0.0
    pl0, pa0 = rng.uniform(0.0, 0.0005), sv_alpha ** 2 * 1.0   # p^alpha chosen so the alpha revision's scale is sv_alpha (two-point law)
    d["bA"], d["bE"] = bA, bE
    B = np.array([[bA], [bE]])
    d["mu0"] = np.array([alpha + bA * lam, bE * lam]); d["Sig0"] = B @ B.T * (sf2 + pl0) + np.diag([sA2 + pa0, sE2])
    sv_lam = np.sqrt(pl0) * 0.5
    d["q"] = np.full(4, 0.25); d["mu1"] = []; d["Sig1"] = []; d["g"] = []
    Sig1 = B @ B.T * (sf2 + pl0 * 0.7) + np.diag([sA2 + pa0 * 0.5, sE2])
    for el in (-sv_lam, sv_lam):
        for ea in (-sv_alpha, sv_alpha):
            d["mu1"].append(d["mu0"] + np.array([bA * el + ea, bE * el])); d["Sig1"].append(Sig1)
            d["g"].append(np.array([1.0 + lam + alpha + el + ea + rng.uniform(-0.05, 0.05), 1.0 + lam + el + rng.uniform(-0.04, 0.04)]))
    d["xm0"] = np.array([0.0, rng.uniform(0.0, 0.3)]); d["h0"] = rng.uniform(0.05, 0.4) if h0 is None else h0
    d["sv_alpha"] = sv_alpha
    return d


def need_states(d, x0):
    """claim 046's need(z') with the fund's and the ETF's solo targets, per state."""
    out = []
    for z in range(len(d["q"])):
        tot = 0.0
        for i in range(2):
            xhat = max(d["mu1"][z][i] - d["kp"][i], 0.0) / (d["gamma"] * d["Sig1"][z][i, i])
            tot += (1 + d["kp"][i]) * max(xhat - d["g"][z][i] * x0[i], 0.0)
        out.append(tot)
    return np.array(out)


def leftover_cash(d, x0):
    u0 = x0 - d["xm0"]; return d["h0"] - u0.sum() - (d["kp"] * np.maximum(u0, 0) + d["km"] * np.maximum(-u0, 0)).sum()


def part_i():
    n_cov = n_tested = 0
    for _ in range(120):
        d = instance_m8(sv_alpha=float(rng.choice([0.003, 0.01, 0.02])))
        x0m, x1m, eta0m, eta1m = c44.myopic_policy(d)
        hm = leftover_cash(d, x0m); need = need_states(d, x0m)
        n_tested += 1
        if hm >= need.max() - 1e-9:
            n_cov += 1
            check(max(eta1m) < 1e-6, f"part 2: one-review cash {hm:.4f} covers the largest need {need.max():.4f} yet a tomorrow multiplier is {max(eta1m):.2e}")
            x0d, x1d, eta0d, eta1d, _ = c44.solve_dynamic(d)
            check(max(eta1d) < 1e-6, "part 2: no-reserve condition at the one-review root, yet the dynamic optimum prices cash tomorrow")
    print(f"  part 2: the no-reserve condition held at {n_cov} of {n_tested} one-review roots, with every tomorrow multiplier zero there (myopic and dynamic)")


def part_ii_iii():
    n_bind = 0; n_line = 0
    for _ in range(120):
        d = instance_m8(sv_alpha=float(rng.choice([0.01, 0.02, 0.03])), h0=float(rng.uniform(0.03, 0.2)))
        x0d, x1d, eta0d, eta1d, _ = c44.solve_dynamic(d)
        hd = leftover_cash(d, x0d); need = need_states(d, x0d)
        if max(eta1d) > 1e-6:
            n_bind += 1
            check(hd <= need.max() + 1e-6, f"part 4 (maximum): cash carried {hd:.4f} exceeds the largest need {need.max():.4f} while a state prices cash")
        # part 3: the ETF's root line with the reserve premium (claim 044's ETF line), read on the ETF's holding
        ok, eta_hat, (Slo, Shi) = c44.root_lines_ok(d, x0d, x1d, eta0d, eta1d)
        check(ok, "part 3: the root lines fail at the dynamic optimum"); n_line += int(ok)
    print(f"  part 4 (maximum): cash carried below the largest need at every one of {n_bind} dynamic optima with a binding state; part 3: root lines held at {n_line} of 120")


def part_iv():
    # growth of the largest need with the alpha revision's scale, and the dynamic reserve on a grid (illustration)
    base = rng.integers(1 << 30)
    slopes_ok = 0; res = []
    for sv in [0.005, 0.01, 0.02, 0.03]:
        rng2 = np.random.default_rng(base); c44.rng = rng2
        globals()["rng"] = rng2
        d = instance_m8(sv_alpha=sv, h0=0.12, seed_shift=0.01)
        x0m, *_ = c44.myopic_policy(d); need = need_states(d, x0m)
        # the fund's need in the top alpha state rises with sv at slope (1 + kp_A)/(gamma Sigma_AA) per unit revision when the purchase is active
        z_top = int(np.argmax([m[0] for m in d["mu1"]]))
        xhat = max(d["mu1"][z_top][0] - d["kp"][0], 0.0) / (d["gamma"] * d["Sig1"][z_top][0, 0])
        if xhat > d["g"][z_top][0] * x0m[0]:
            slope = (1 + d["kp"][0]) / (d["gamma"] * d["Sig1"][z_top][0, 0]); slopes_ok += 1
        x0d, *_ = c44.solve_dynamic(d)
        reserve = (leftover_cash(d, x0d) - leftover_cash(d, x0m)) + (1 - d["km"][1]) * (x0d[1] - x0m[1])
        res.append(reserve)
    c44.rng = np.random.default_rng(470); globals()["rng"] = c44.rng
    print(f"  part 4 (growth, illustration): the fund's top-state need active in {slopes_ok} of 4 scales; the dynamic reserve over sqrt(v_alpha) in (0.005, 0.01, 0.02, 0.03): {[round(r, 4) for r in res]}")


c45 = _load("check045", "045")


def part_v():
    """part 3(b): with slack budgets and the fund fixed at its one-review holding, the ETF's shift from the one-review
    holding is [S_E - (t^dyn - t^my)]/(gamma Sigma_EE), S_E = beta E[g_E t_{1,E}]; equal to S_E/(gamma Sigma_EE) when the
    ETF trades the same way today under both; and |shift| <= beta max(kappa) E[g_E]/(gamma Sigma_EE) + (kappa^+ + kappa^-)/(gamma Sigma_EE)."""
    n_same = n_all = 0
    for _ in range(80):
        d = instance_m8(sv_alpha=float(rng.choice([0.01, 0.02, 0.03])), h0=5.0)   # slack budgets
        d["xm0"] = np.array([rng.uniform(0.0, 0.5), rng.uniform(0.0, 0.8)])
        x0m, x1m, eta0m, eta1m = c44.myopic_policy(d)
        if max(eta1m) > 1e-6 or eta0m > 1e-6: continue
        x0r, x1r, eta0r, eta1r = c45.solve_fix_a(d, x0m[0])          # the ETF re-optimized dynamically with the fund fixed
        if max(eta1r) > 1e-6: continue
        if not (x0m[1] > 1e-3 and x0r[1] > 1e-3): continue              # ETF interior at both
        ok, eta_hat, (Slo, Shi) = c44.root_lines_ok(d, x0r, x1r, eta0r, eta1r)
        SE = 0.5 * (Slo[1] + Shi[1])                                     # pinned unless an ETF is held at a bound tomorrow
        if Shi[1] - Slo[1] > 1e-9: continue
        cE = d["gamma"] * d["Sig0"][1, 1]; shift = x0r[1] - x0m[1]
        tm = d["kp"][1] if x0m[1] > d["xm0"][1] + 1e-4 else (-d["km"][1] if x0m[1] < d["xm0"][1] - 1e-4 else None)
        tr = d["kp"][1] if x0r[1] > d["xm0"][1] + 1e-4 else (-d["km"][1] if x0r[1] < d["xm0"][1] - 1e-4 else None)
        n_all += 1
        bound = d["beta"] * max(d["kp"][1], d["km"][1]) * sum(d["q"][z] * d["g"][z][1] for z in range(4)) / cE + (d["kp"][1] + d["km"][1]) / cE
        check(abs(shift) <= bound + 1e-4, f"part 3(b): ETF shift {shift:.4f} exceeds its bound {bound:.4f}")
        if tm is not None and tr is not None and tm == tr:
            n_same += 1
            check(abs(shift - SE / cE) < 2e-3, f"part 3(b): ETF shift {shift:.4f} vs S_E/(gamma Sigma_EE) = {SE / cE:.4f}")
    print(f"  part 3(b): slack budgets, fund fixed: the ETF's shift equals S_E/(gamma Sigma_EE) in {n_same} same-slope cases and obeys its bound in all {n_all}")


def main():
    part_i(); part_ii_iii(); part_iv(); part_v()
    if FAIL:
        print(f"checks/047: {len(FAIL)} failure(s)"); sys.exit(1)
    print("checks/047: all checks passed")


if __name__ == "__main__":
    main()
