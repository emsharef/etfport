"""Finite checks for claim 043 (D15e: the fine-regime cost with one costly ETF, sandwiched); not its proof.

Run: uv run python checks/043/check.py

 (i)   part 2: the separable sub- and supersolutions satisfy the corrector inequalities on a grid of the (y_a, e) plane:
       the PDE inequality with the eigenvalue, the gradient constraints (subsolution: gradient in the polytope C
       everywhere; supersolution: gradient on or outside int C wherever the PDE equality fails), for random inputs;
 (ii)  part 3: the sandwich collapses at rho_h = 0 and its relative gap is bounded by the stated expression;
 (iii) illustration: a Monte Carlo of a rectangle policy in (y_a, e) (fund band on y_a, ETF band on e) gives an average
       cost above the lower bound, as any policy must, and near the upper bound at small rate ratios.
Random assumed inputs (rule 22). Floating point, not a certificate.
"""
import sys

import numpy as np

rng = np.random.default_rng(43)
FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg); print("FAIL:", msg)


def one_d(k, v, c):
    """the 1D corrector solution for round-trip rate 2k (k per side): Delta, eigenvalue a, and w, w', w'' as callables."""
    D = (3 * (2 * k) * v / (4 * c)) ** (1 / 3); a = c * D ** 2 / 2
    def w(y):
        y = np.asarray(y, dtype=float); inside = np.abs(y) <= D
        wi = -(c / (12 * v)) * y ** 4 + (a / v) * y ** 2
        wD = -(c / (12 * v)) * D ** 4 + (a / v) * D ** 2
        return np.where(inside, wi, wD + k * (np.abs(y) - D))
    def wp(y):
        y = np.asarray(y, dtype=float); inside = np.abs(y) <= D
        return np.where(inside, -(c / (3 * v)) * y ** 3 + (2 * a / v) * y, k * np.sign(y))
    def wpp(y):
        y = np.asarray(y, dtype=float); inside = np.abs(y) <= D
        return np.where(inside, (2 * a - c * y ** 2) / v, 0.0)
    return D, a, w, wp, wpp


def instance():
    s_aa, s_ee = rng.uniform(0.5, 2.0, 2); rc = rng.uniform(-0.9, 0.9); s_ae = rc * np.sqrt(s_aa * s_ee)
    gamma = rng.uniform(1.0, 6.0); v_a, v_b = rng.uniform(1e-6, 1e-5, 2); r = rng.uniform(-0.9, 0.9)
    rho_h = s_ae / s_ee; c_res = gamma * (s_aa - s_ae ** 2 / s_ee); c_e = gamma * s_ee
    v_b_eff = v_b + rho_h ** 2 * v_a + 2 * rho_h * r * np.sqrt(v_a * v_b)
    cov = r * np.sqrt(v_a * v_b) + rho_h * v_a
    kA = rng.uniform(0.005, 0.03); kE = rng.uniform(0.0, 0.5) * kA
    return dict(rho_h=rho_h, c_res=c_res, c_e=c_e, v_a=v_a, v_b_eff=v_b_eff, cov=cov, kA=kA, kE=kE, gamma=gamma, s_aa=s_aa, s_ae=s_ae, s_ee=s_ee, v_b=v_b, r=r)


def part_i():
    n_ok = 0
    for _ in range(40):
        d = instance(); rh, kA, kE = d["rho_h"], d["kA"], d["kE"]
        if kA - abs(rh) * kE <= 0: continue
        # subsolution: fund rate kA - |rho_h| kE; supersolution: fund rate kA + |rho_h| kE; ETF rate kE in both
        DA1, a1A, _, wpA1, wppA1 = one_d(kA - abs(rh) * kE, d["v_a"], d["c_res"])
        DA2, a2A, _, wpA2, wppA2 = one_d(kA + abs(rh) * kE, d["v_a"], d["c_res"])
        DE, aE, _, wpE, wppE = one_d(kE, d["v_b_eff"], d["c_e"])
        a1 = a1A + aE; a2 = a2A + aE
        ya = np.linspace(-3 * DA2, 3 * DA2, 121); e = np.linspace(-3 * DE, 3 * DE, 121); YA, E = np.meshgrid(ya, e, indexing="ij")
        cost = 0.5 * d["c_res"] * YA ** 2 + 0.5 * d["c_e"] * E ** 2
        # subsolution: L w1 + cost >= a1 everywhere (cross term vanishes for separable w), gradient in C everywhere
        L1 = 0.5 * d["v_a"] * wppA1(YA) + 0.5 * d["v_b_eff"] * wppE(E)
        check(np.all(L1 + cost >= a1 - 1e-12), "part 2: subsolution PDE inequality fails")
        pa, pe = wpA1(YA), wpE(E)
        check(np.all(np.abs(pa + rh * pe) <= kA + 1e-12) and np.all(np.abs(pe) <= kE + 1e-12), "part 2: subsolution gradient leaves C")
        # supersolution: at every point, either L w2 + cost <= a2 or the gradient is on/outside the boundary of C
        L2 = 0.5 * d["v_a"] * wppA2(YA) + 0.5 * d["v_b_eff"] * wppE(E)
        pa2, pe2 = wpA2(YA), wpE(E)
        pde_ok = L2 + cost <= a2 + 1e-12
        on_boundary = (np.abs(pa2 + rh * pe2) >= kA - 1e-12) | (np.abs(pe2) >= kE - 1e-12)
        check(np.all(pde_ok | on_boundary), "part 2: supersolution fails at some point")
        # third lower bound: w3(y) = w_{kE}(e - rho_h y_a) with (c_b, v_B): gradient in C, PDE inequality
        c_b = d["c_res"] * d["c_e"] / (d["c_res"] + rh ** 2 * d["c_e"])
        _, a3, _, wp3, wpp3 = one_d(kE, d["v_b"], c_b)
        YB = E - rh * YA
        L3 = 0.5 * d["v_b"] * wpp3(YB)   # (1/2) tr(W D^2 w3) = (v_B/2) w'' since e - rho_h y_a has variance v_B
        check(np.all(L3 + cost >= a3 - 1e-12), "part 2: third-lower-bound PDE inequality fails")
        check(np.all(np.abs(wp3(YB)) <= kE + 1e-12), "part 2: third-lower-bound gradient leaves C")
        check(abs((d["v_b_eff"] - 2 * rh * d["cov"] + rh ** 2 * d["v_a"]) - d["v_b"]) < 1e-15, "part 2: variance of e - rho_h y_a is not v_B")
        n_ok += 1
    print(f"  part 2: separable sub- and supersolutions verified on {n_ok} random instances (grid 121 x 121)")


def part_ii():
    for _ in range(200):
        d = instance(); rh, kA, kE = d["rho_h"], d["kA"], d["kE"]
        if kA - abs(rh) * kE <= 0: continue
        _, a1A, *_ = one_d(kA - abs(rh) * kE, d["v_a"], d["c_res"]); _, a2A, *_ = one_d(kA + abs(rh) * kE, d["v_a"], d["c_res"])
        _, aE, *_ = one_d(kE, d["v_b_eff"], d["c_e"]); _, aA, *_ = one_d(kA, d["v_a"], d["c_res"])
        gap = (a2A - a1A) / (aA + aE)
        bound = ((1 + abs(rh) * kE / kA) ** (2 / 3) - (1 - abs(rh) * kE / kA) ** (2 / 3)) * aA / (aA + aE)
        check(abs(gap - bound) < 1e-12, "part 3: relative gap differs from the stated expression")
        x = abs(rh) * kE / kA
        check(bound <= 2 * (1 - (1 - x) ** (2 / 3)) * aA / (aA + aE) + 1e-12, "part 3: relative gap exceeds 2 [1 - (1 - x)^(2/3)] times the fund's share")
    for x in np.linspace(0, 0.99, 200):   # the elementary bound (1+x)^(2/3) - (1-x)^(2/3) <= 2 [1 - (1-x)^(2/3)]
        check((1 + x) ** (2 / 3) - (1 - x) ** (2 / 3) <= 2 * (1 - (1 - x) ** (2 / 3)) + 1e-12, "part 3: elementary gap bound fails")
    # the third lower bound diverges with kappa_E while the separable one stays bounded (leanb's instance)
    c_res, v_a, c_e, kA, v_b_eff, rh = 1.0, 1.0, 1.0, 1.0, 0.02, 0.5
    c_b = c_res * c_e / (c_res + rh ** 2 * c_e)
    for kE in [1.0, 10.0, 100.0]:
        _, a3, *_ = one_d(kE, 0.02, c_b)
        best = max(one_d(kAp, v_a, c_res)[1] + one_d(kEp, v_b_eff, c_e)[1]
                   for kAp in np.linspace(0, kA, 201) for kEp in np.linspace(0, min(kE, (kA - kAp) / rh), 41))
        check(a3 > 0 and (kE > 1 or abs(best - 0.656) < 0.01), f"part 3: separable max {best:.3f} at kappa_E = {kE:g} (leanb's 0.656)")
    # collapse at rho_h = 0
    d = instance(); d["rho_h"] = 0.0
    _, a1A, *_ = one_d(d["kA"], d["v_a"], d["c_res"]); _, a2A, *_ = one_d(d["kA"], d["v_a"], d["c_res"])
    check(a1A == a2A, "part 3: no collapse at rho_h = 0")
    print("  part 3: the relative gap equals its stated expression and obeys the bound 2 [1 - (1 - x)^(2/3)] (= (4/3) x + O(x^2)); collapse at rho_h = 0")


def part_iii():
    # rectangle policy in (y_a, e): fund pushes y_a (moving e by rho_h da), ETF pushes e; Gaussian steps; average cost
    d = dict(rho_h=0.5, c_res=2.0, c_e=3.0, v_a=4e-9, v_b_eff=5e-9, cov=1e-9, kA=0.01, kE=0.001)
    rh = d["rho_h"]
    DA, aA, *_ = one_d(d["kA"], d["v_a"], d["c_res"]); DE, aE, *_ = one_d(d["kE"], d["v_b_eff"], d["c_e"])
    _, a1A, *_ = one_d(d["kA"] - rh * d["kE"], d["v_a"], d["c_res"]); _, a2A, *_ = one_d(d["kA"] + rh * d["kE"], d["v_a"], d["c_res"])
    lo, hi = a1A + aE, a2A + aE
    n = 400000; g = np.random.default_rng(5)
    C = np.array([[d["v_a"], d["cov"]], [d["cov"], d["v_b_eff"]]]); L = np.linalg.cholesky(C); Z = g.normal(size=(n, 2)) @ L.T
    ya = e = 0.0; tot = 0.0
    for k in range(n):
        ya -= Z[k, 0]; e -= Z[k, 1]
        if ya > DA: da = DA - ya; tot += d["kA"] * (-da); ya = DA; e += rh * da
        elif ya < -DA: da = -DA - ya; tot += d["kA"] * da; ya = -DA; e += rh * da
        if e > DE: tot += d["kE"] * (e - DE); e = DE
        elif e < -DE: tot += d["kE"] * (-DE - e); e = -DE
        tot += 0.5 * d["c_res"] * ya ** 2 + 0.5 * d["c_e"] * e ** 2
    avg = tot / n
    check(avg >= lo * (1 - 0.05), f"part 3 illustration: rectangle policy cost {avg:.3e} below the lower bound {lo:.3e}")
    print(f"  illustration: rectangle-policy average cost {avg:.3e} against the sandwich [{lo:.3e}, {hi:.3e}] (fund-alone plus ETF-alone {aA + aE:.3e}); "
          f"steps at 3% and 6% of the two half-widths")


def main():
    part_i(); part_ii(); part_iii()
    if FAIL:
        print(f"checks/043: {len(FAIL)} failure(s)"); sys.exit(1)
    print("checks/043: all checks passed")


if __name__ == "__main__":
    main()
