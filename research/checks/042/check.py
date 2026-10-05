"""Finite checks for claim 042 (D15e: the fund's fine-regime band with one costly ETF); not its proof.

Run: uv run python checks/042/check.py

 (i)   part 1: the error-coordinate identity for the two-instrument tracking loss on random covariances;
 (ii)  part 3: the one-instrument fine-regime law Delta^3 = 3 (kappa^+ + kappa^-) v / (4 c): the ergodic HJB solution's
       smooth fit, and a Monte Carlo of a reflected random walk's average cost over a grid of half-widths, whose minimizer
       is at the law's value within the grid;
 (iii) part 2: the two exact reductions as Monte Carlo cost identities: with the ETF continuously hedged the two-instrument
       loss equals the one-instrument loss with (c^res, v_A); with the ETF frozen it equals the one with (gamma Sigma_AA, v^idle);
 (iv)  part 4: the dimensionless ratio xi and the two end laws; the idle fraction of a reflected walk in the fine regime
       tends to one as the step shrinks, at every rate ratio (illustration).
Random assumed inputs (rule 22). Floating point, not a certificate.
"""
import sys

import numpy as np

rng = np.random.default_rng(42)
FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg); print("FAIL:", msg)


def part_i():
    for _ in range(200):
        s_aa, s_ee = rng.uniform(0.5, 2.0, 2); rc = rng.uniform(-0.95, 0.95); s_ae = rc * np.sqrt(s_aa * s_ee)
        gamma = rng.uniform(1.0, 8.0); ya, yb = rng.normal(size=2)
        loss = 0.5 * gamma * (s_aa * ya ** 2 + 2 * s_ae * ya * yb + s_ee * yb ** 2)
        rho_h = s_ae / s_ee; c_res = gamma * (s_aa - s_ae ** 2 / s_ee); e = yb + rho_h * ya
        check(abs(loss - (0.5 * c_res * ya ** 2 + 0.5 * gamma * s_ee * e ** 2)) < 1e-12, "part 1: error-coordinate identity fails")
        # the frozen-ETF form: curvature gamma Sigma_AA on y_a + rho' y_b, rho' = Sigma_AE / Sigma_AA
        rho_p = s_ae / s_aa
        check(abs(loss - (0.5 * gamma * s_aa * (ya + rho_p * yb) ** 2 + 0.5 * gamma * (s_ee - s_ae ** 2 / s_aa) * yb ** 2)) < 1e-12, "part 2(c): frozen-ETF form fails")
    print("  part 1: the error-coordinate identity and the frozen-ETF form hold on 200 random covariances")


def law(kp, km, v, c):
    return (3 * (kp + km) * v / (4 * c)) ** (1 / 3)


def band_cost(kp, km, v, c, delta, n=400000, seed=0):
    """average cost per step of the band policy [-delta, delta] for a target with Gaussian steps of variance v."""
    r = np.random.default_rng(seed)
    y = 0.0; steps = r.normal(scale=np.sqrt(v), size=n); tot = 0.0
    for s in steps:
        y -= s                       # the target moves; the gap moves opposite
        if y > delta: tot += kp * (y - delta); y = delta
        elif y < -delta: tot += km * (-delta - y); y = -delta
        tot += 0.5 * c * y * y
    return tot / n


def part_ii():
    # smooth-fit algebra: w'' = (2 lambda - c y^2)/v vanishes at +-Delta iff lambda = c Delta^2/2; the gradient change
    # w'(Delta) - w'(-Delta) = (4 c Delta^3 / 3)/v equals kappa^+ + kappa^- iff Delta^3 = 3 (kappa^+ + kappa^-) v/(4c)
    for _ in range(50):
        kp, km, v, c = rng.uniform(0.001, 0.02), rng.uniform(0.001, 0.02), rng.uniform(1e-5, 1e-3), rng.uniform(0.5, 5.0)
        D = law(kp, km, v, c); lam = c * D ** 2 / 2
        wpp = lambda y: (2 * lam - c * y ** 2) / v
        check(abs(wpp(D)) < 1e-12 and abs(wpp(-D)) < 1e-12, "part 3: smooth fit fails")
        grad_change = (2 * lam * 2 * D - 2 * c * D ** 3 / 3) / v
        check(abs(grad_change - (kp + km)) < 1e-12, "part 3: gradient change differs from the round-trip rate")
        # the average holding cost c Delta^2/6 plus trading (kappa^+ + kappa^-) v/(4 Delta) equals lambda
        check(abs(c * D ** 2 / 6 + (kp + km) * v / (4 * D) - lam) < 1e-12, "part 3: cost split differs from lambda")
    # Monte Carlo: the minimizer of the band cost over a grid around the law (fine regime: step << width)
    kp, km, c = 0.01, 0.01, 2.0; v = 8.8e-13
    D = law(kp, km, v, c)                     # about 1.9e-5; step 9.4e-7, so the step is 5% of the half-width (fine regime)
    grid = D * np.linspace(0.6, 1.5, 19)
    costs = [band_cost(kp, km, v, c, d, n=300000, seed=k) for k, d in enumerate(grid)]
    best = grid[int(np.argmin(costs))]
    check(abs(best / D - 1) < 0.15, f"part 3: Monte Carlo minimizer {best:.4f} vs law {D:.4f}")
    print(f"  part 3: smooth-fit algebra holds; Monte Carlo band-cost minimizer {best:.3e} vs the law's {D:.3e} (grid step 5%)")


def part_iii():
    s_aa, s_ee, rc, gamma = 1.0, 0.8, 0.6, 4.0; s_ae = rc * np.sqrt(s_aa * s_ee)
    v_a, v_b, r = 4e-6, 3e-6, 0.3
    rho_h = s_ae / s_ee; rho_p = s_ae / s_aa; c_res = gamma * (s_aa - s_ae ** 2 / s_ee)
    v_idle = v_a + rho_p ** 2 * v_b + 2 * rho_p * r * np.sqrt(v_a * v_b)
    n = 200000; g = np.random.default_rng(3)
    Z = g.normal(size=(n, 2)); da = np.sqrt(v_a) * Z[:, 0]; db = np.sqrt(v_b) * (r * Z[:, 0] + np.sqrt(1 - r ** 2) * Z[:, 1])
    kp = km = 0.01
    # (b) ETF continuously hedged: b - b* = -rho_h (a - a*) at every step; the two-instrument loss along a fund band policy
    #     equals the one-instrument loss with curvature c^res and target innovations da
    D = law(kp, km, v_a, c_res); ya = 0.0; two = one = 0.0
    for k in range(n):
        ya -= da[k]
        if ya > D: two += kp * (ya - D); one += kp * (ya - D); ya = D
        elif ya < -D: two += km * (-D - ya); one += km * (-D - ya); ya = -D
        yb = -rho_h * ya
        two += 0.5 * gamma * (s_aa * ya ** 2 + 2 * s_ae * ya * yb + s_ee * yb ** 2); one += 0.5 * c_res * ya ** 2
    check(abs(two - one) < 1e-9 * n, "part 2(b): hedged-ETF two-instrument loss differs from the residual one-instrument loss")
    # (c) ETF frozen at b = b*_0: the two-instrument loss along a fund band on the effective target equals the one-instrument
    #     loss with curvature gamma Sigma_AA and innovations da + rho' db (variance v^idle), plus the ETF's own term
    D2 = law(kp, km, v_idle, gamma * s_aa); z = 0.0; yb = 0.0; two = one = 0.0
    for k in range(n):
        yb -= db[k]                    # b fixed, b* moves
        z -= (da[k] + rho_p * db[k])   # z = y_a + rho' y_b, the gap to the effective target
        if z > D2: two += kp * (z - D2); one += kp * (z - D2); z = D2
        elif z < -D2: two += km * (-D2 - z); one += km * (-D2 - z); z = -D2
        ya = z - rho_p * yb
        two += 0.5 * gamma * (s_aa * ya ** 2 + 2 * s_ae * ya * yb + s_ee * yb ** 2)
        one += 0.5 * gamma * s_aa * z ** 2 + 0.5 * gamma * (s_ee - s_ae ** 2 / s_aa) * yb ** 2
    check(abs(two - one) < 1e-9 * n, "part 2(c): frozen-ETF two-instrument loss differs from the effective one-instrument loss")
    print(f"  part 2: hedged-ETF and frozen-ETF reductions hold as path identities (half-widths {D:.4f} with c^res, v_A and {D2:.4f} with gamma Sigma_AA, v^idle)")


def part_iv():
    # xi and the two end laws; idle fraction of a reflected walk tends to one as the step shrinks, at every rate ratio
    s_aa, s_ee, rc, gamma = 1.0, 0.8, 0.6, 4.0; s_ae = rc * np.sqrt(s_aa * s_ee)
    v_a, v_b, r = 4e-6, 3e-6, 0.3; rho_h = s_ae / s_ee; rho_p = s_ae / s_aa
    c_res = gamma * (s_aa - s_ae ** 2 / s_ee); v_idle = v_a + rho_p ** 2 * v_b + 2 * rho_p * r * np.sqrt(v_a * v_b)
    v_b_eff = v_b + rho_h ** 2 * v_a + 2 * rho_h * r * np.sqrt(v_a * v_b)
    kA = 0.02
    for kE in [0.0002, 0.002, 0.02, 0.2]:
        xi3 = (kE / kA) * (v_b_eff / v_a) * (c_res / (gamma * s_ee))
        D_free = law(kA / 2, kA / 2, v_a, c_res); D_frozen = law(kA / 2, kA / 2, v_idle, gamma * s_aa)
        check(abs((D_frozen / D_free) ** 3 - (1 - rc ** 2) * v_idle / v_a) < 1e-12, "part 4: end ratio differs from ((1 - rc^2) v^idle / v_A)^(1/3)")
        # idle fraction of the ETF's own reflected walk at its band, as the step shrinks (fine regime)
        fr = []
        for scale in [1.0, 1e-4, 1e-8]:     # the step-to-width ratio falls like v^(1/6), so the fine regime needs tiny steps
            v = v_b_eff * scale; D = law(kE / 2, kE / 2, v, gamma * s_ee); y = 0.0; trades = 0; n = 100000
            for s in np.random.default_rng(7).normal(scale=np.sqrt(v), size=n):
                y -= s
                if y > D: y = D; trades += 1
                elif y < -D: y = -D; trades += 1
            fr.append(1 - trades / n)
        check(fr[0] <= fr[1] <= fr[2] and fr[-1] > 0.85, f"part 4: idle fraction does not approach one ({fr})")
        print(f"    kappa_E/kappa_A = {kE / kA:g}: xi^3 = {xi3:.3g}; ETF idle fraction as the step shrinks {[round(f, 3) for f in fr]}")
    print("  part 4: end laws consistent; the idle fraction rises toward one at every rate ratio while the end widths differ;\n"
          "          at the illustrative inputs the ETF at basis-point rates is in the coarse regime (step above its static width) unless v is tiny")


def main():
    part_i(); part_ii(); part_iii(); part_iv()
    if FAIL:
        print(f"checks/042: {len(FAIL)} failure(s)"); sys.exit(1)
    print("checks/042: all checks passed")


if __name__ == "__main__":
    main()
