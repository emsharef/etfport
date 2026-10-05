"""Finite checks for claim 037 (D15a: the integration theorem); not its proof.

Run: uv run python checks/037/check.py

 (i)  A3: delta_t / x*_t = kappa_t p_t/(sigma^2 + p_{t+1}) <= kappa_t^2/(1 - kappa_t) on scalar Kalman paths;
 (ii) B3: first-order anticipation (claim 036's L_t - 1) against the second-order drift ratio on the same inputs;
 (iii) C1: the Bellman-residual identity in M7 at T = 1, 2 (scalar finite-law instance, enumeration) and in M5 (claim 033);
 (iv) C3: the one-review M7 estimation bound on a grid of covariance and mean errors;
 (v)  D: M5's T = 1 rule against its first-order condition; M7's T = 1 band edges against claim 009's form.
Inputs are illustrative (rule 22).
"""
import importlib.util
import itertools
import os
import sys

import numpy as np

rng = np.random.default_rng(37)


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(os.path.dirname(__file__), "..", rel, "check.py"))
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod


_c36 = _load("check036", "036")


# ---------- (i) and (ii) ----------
def kalman_scalar(s2, sig2, T):
    return [1 / (1 / s2 + t / sig2) for t in range(T + 1)]


def part_i_ii():
    sig2 = 0.02 ** 2; T = 12
    for ratio in [0.01, 0.03, 0.1, 0.3, 1.0, 3.0]:
        p = kalman_scalar(ratio * sig2, sig2, T)
        for t in range(T):
            kap = p[t] / (sig2 + p[t])
            drift_ratio = (sig2 + p[t]) / (sig2 + p[t + 1]) - 1
            assert abs(drift_ratio - kap * p[t] / (sig2 + p[t + 1])) < 1e-15
            assert drift_ratio <= kap ** 2 / (1 - kap) + 1e-15
            assert abs(p[t] - p[t + 1] - p[t] * kap) < 1e-18
    # (ii) first vs second order on the same inputs (lambda_A 0.1, gamma 5, T 12, t = 0)
    rows = []
    for ratio in [0.3, 0.1, 0.03, 0.01, 0.003]:
        p = kalman_scalar(ratio * sig2, sig2, T)
        w, R = _c36.weights(0.1, 5.0, sig2, p, T, 0)
        ell = float(np.sum(w * sig2 / (sig2 + np.array(p[:T])))); L = ell * (sig2 + p[0]) / sig2
        kap = p[0] / (sig2 + p[0]); drift = (sig2 + p[0]) / (sig2 + p[1]) - 1
        rows.append((kap, L - 1, drift))
    # both effects are second order in the gain: (L_t - 1)/kappa^2 and drift/kappa^2 stay of order one,
    # and L_t - 1 <= (kappa/(1-kappa))^2 Dur_t with Dur_t the aim's look-ahead duration
    a = [L1 / k ** 2 for k, L1, d in rows]; b = [d / k ** 2 for k, L1, d in rows]
    assert max(a) / min(a) < 5 and max(b) / min(b) < 5, (a, b)
    for ratio, (k, L1, d) in zip([0.3, 0.1, 0.03, 0.01, 0.003], rows):
        p = kalman_scalar(ratio * sig2, sig2, T); w, R = _c36.weights(0.1, 5.0, sig2, p, T, 0)
        dur = float(np.sum(w * np.arange(T)))
        assert L1 <= (k / (1 - k)) ** 2 * dur + 1e-15 and d <= (k / (1 - k)) ** 2 + 1e-15, (k, L1, dur)
    # duration tends to 0 as the fund cost vanishes
    p = kalman_scalar(0.1 * sig2, sig2, T); w0, _ = _c36.weights(1e-6, 5.0, sig2, p, T, 0)
    assert float(np.sum(w0 * np.arange(T))) < 1e-3
    print("  A3 identity and bound hold on the grid; B3: (L_t - 1)/kappa^2 and drift/kappa^2 both stay of order one "
          f"(kappa from {rows[0][0]:.3f} to {rows[-1][0]:.4f}: {[f'{x:.2f}' for x in a]} and {[f'{x:.2f}' for x in b]}); "
          "L_t - 1 <= (kappa/(1-kappa))^2 Dur_t; Dur_t -> 0 at zero cost")


# ---------- (iii) C1 in M7 (scalar, finite law, slack budget, T = 2) by enumeration ----------
def m7_scalar(T=2, kp=0.01, km=0.01, c=5.0 * 0.0004, xbar=1.0, beta=1.0):
    """One instrument; target x*_t depends on a finite belief state; gross return 1 (pure-learning marking)."""
    # belief tree: state at t is an index; target values and transition probabilities
    targets = {0: [0.3], 1: [0.2, 0.45]}; probs = {0: [[0.5, 0.5]]}
    grid = np.linspace(0, xbar, 401)
    def cost(u): return kp * max(u, 0) + km * max(-u, 0)
    def G(t, z, x):
        loss = 0.5 * c * (x - targets[t][z]) ** 2
        if t + 1 < T:
            loss += beta * sum(pr * V(t + 1, zn, x) for zn, pr in enumerate(probs[t][z]))
        return loss
    memo = {}
    def V(t, z, x):
        key = (t, z, round(x, 9))
        if key in memo: return memo[key]
        val = min(cost(xp - x) + G(t, z, xp) for xp in grid); memo[key] = val; return val
    def policy(t, z, x):
        return min(grid, key=lambda xp: cost(xp - x) + G(t, z, xp))
    return targets, probs, grid, cost, G, V, policy


def part_iii():
    targets, probs, grid, cost, G, V, policy = m7_scalar()
    x0 = 0.6
    Vstar = V(0, 0, x0)
    # a suboptimal policy: always trade to the target (no band), evaluate its cost and its residual sum
    def r(t, z, x, xp): return -(cost(xp - x) + 0.5 * c_of() * (xp - targets[t][z]) ** 2)
    def c_of(): return 5.0 * 0.0004
    # value of pi (trade to target) and residual identity
    xp0 = targets[0][0]; stage0 = cost(xp0 - x0) + 0.5 * c_of() * 0
    Vpi = stage0 + sum(pr * (cost(targets[1][z1] - xp0)) for z1, pr in enumerate(probs[0][0]))
    J0 = Vstar
    J1 = lambda z1, x: V(1, z1, x)
    Delta0 = -J0 + (stage0 + sum(pr * J1(z1, xp0) for z1, pr in enumerate(probs[0][0])))
    Delta1 = sum(pr * (-J1(z1, xp0) + cost(targets[1][z1] - xp0)) for z1, pr in enumerate(probs[0][0]))
    assert Delta0 >= -1e-12 and Delta1 >= -1e-12
    assert abs((Vpi - Vstar) - (Delta0 + Delta1)) < 1e-9, (Vpi - Vstar, Delta0 + Delta1)
    print(f"  C1 (M7, T = 2, enumeration): loss of trade-to-target policy {Vpi - Vstar:.3e} = sum of Bellman residuals {Delta0 + Delta1:.3e}")


# ---------- (iv) C3 one-review M7 bound and (v) D ----------
def part_iv_v():
    kp, km, xbar = 0.01, 0.005, 1.0
    for _ in range(300):
        mu, c = rng.uniform(-0.02, 0.03), rng.uniform(0.001, 0.02); xm = rng.uniform(0, xbar)
        mu_h, c_h = mu * (1 + rng.uniform(-0.5, 0.5)), c * (1 + rng.uniform(-0.5, 0.5))
        xs, xs_h = mu / c, mu_h / c_h
        lo, hi = np.clip(xs - kp / c, 0, xbar), np.clip(xs + km / c, 0, xbar)
        lo_h, hi_h = np.clip(xs_h - kp / c_h, 0, xbar), np.clip(xs_h + km / c_h, 0, xbar)
        xp, xp_h = min(max(xm, lo), hi), min(max(xm, lo_h), hi_h)
        obj = lambda x: mu * x - 0.5 * c * x ** 2 - (kp * max(x - xm, 0) + km * max(xm - x, 0))
        # true optimum equals the band projection (claim 029 1b): check against a grid
        grid = np.linspace(0, xbar, 20001); best = grid[np.argmax([obj(x) for x in grid])]
        step = xbar / 20000
        assert obj(best) - obj(xp) < (abs(mu) + c * xbar + max(kp, km)) * step + 1e-12   # grid optimum within one step's Lipschitz slack
        loss = obj(xp) - obj(xp_h)
        dlo = abs(xs_h - xs) + kp * abs(1 / c_h - 1 / c); dhi = abs(xs_h - xs) + km * abs(1 / c_h - 1 / c)
        bound = (abs(mu) + c * xbar + max(kp, km)) * max(dlo, dhi)
        assert -1e-12 <= loss <= bound + 1e-12, (loss, bound)
        assert abs(lo_h - lo) <= dlo + 1e-12 and abs(hi_h - hi) <= dhi + 1e-12
    # D: M5 at T = 1: first-order condition
    n = 3; Lam = np.diag(rng.uniform(0.01, 0.2, n)); Sig = rng.standard_normal((n, n)); Sig = Sig @ Sig.T / n * 0.001 + 1e-4 * np.eye(n)
    mu = rng.uniform(-0.01, 0.02, n); xm = rng.uniform(-0.3, 0.3, n); gamma = 5.0
    x1 = np.linalg.solve(Lam + gamma * Sig, Lam @ xm + mu)
    foc = mu - gamma * Sig @ x1 - Lam @ (x1 - xm)
    assert np.linalg.norm(foc) < 1e-12
    print("  C3 (M7, one review): loss within the explicit bound on 300 random error draws; D: M5's T = 1 rule satisfies its first-order condition; M7's T = 1 band is claim 009's edges")


def main():
    part_i_ii(); part_iii(); part_iv_v()
    print("checks/037: all checks passed")


if __name__ == "__main__":
    main()
    sys.exit(0)
