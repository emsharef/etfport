"""Finite checks for claim 032 (D12: the learning factor on the aim and the two speeds of the pooled prior); not its proof.

Run: uv run python checks/032/check.py

Separated instances (3 homogeneous funds, 2 ETFs, 2 factors; ETFs costless, residual-free, fee-free; B^E invertible),
s_bar in {0, 0.0035}, gamma in {2, 5, 10}, T in {4, 8}, rho = 1:
 (1) P^alpha_t = p^c_t Pi_c + p^r_t Pi_r with 1/p^c = 1/(s^2 + N s_bar^2) + t/sigma^2, 1/p^r = 1/s^2 + t/sigma^2;
 (2) Gamma^A_t has eigenvalues g^c_t >= g^r_t from the two scalar Riccati recursions, equal iff s_bar = 0;
 (3) the fund aim equals ell^dir alpha_hat^dir/(gamma sigma^2) with ell from the displayed weights (sum 1, bounded);
     the aim exceeds the myopic shrunk Markowitz position by the learning factor >= 1;
 (4) the ETF exposure is the myopic rule;
 (5) observations: ell increases with lambda_A; ell^c <= ell^r.
"""
import itertools
import os
import sys

import numpy as np

import importlib.util

def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(os.path.dirname(__file__), "..", rel, "check.py"))
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod

_c30 = _load("check030", "030"); _c31 = _load("check031", "031")
kalman_path, recursion, rng, make = _c30.kalman_path, _c30.recursion, _c30.rng, _c31.make

TOL = 1e-9


def scalar_recursion(lamA, gamma, sig2, p_path, T, rho=1.0):
    a = 0.0; A = [0.0] * (T + 1); d = [0.0] * T
    for t in range(T - 1, -1, -1):
        d[t] = lamA + gamma * (sig2 + p_path[t]) + rho * a
        a = lamA - lamA ** 2 / d[t]; A[t] = a
    return A, d


def ell_weights(lamA, gamma, sig2, p_path, T, t, rho=1.0):
    A, d = scalar_recursion(lamA, gamma, sig2, p_path, T, rho)
    ws = []
    for s in range(t, T):
        prod = 1.0
        for u in range(t, s):
            prod *= rho * A[u + 1] / (d[u] - lamA)
        ws.append(prod * gamma * (sig2 + p_path[s]) / (d[s] - lamA))
    ws = np.array(ws)
    ell = float(np.sum(ws * sig2 / (sig2 + np.array(p_path[t:T]))))
    return ws, ell, A


def run(s_bar, gamma, T, lamA=0.1):
    I = make((3, 2, 2), gamma, T)
    N, K = I["N"], I["K"]
    s = 0.0035; sig2 = 0.02 ** 2
    I["P0"][K:, K:] = s_bar ** 2 * np.ones((N, N)) + s ** 2 * np.eye(N)
    I["Lam"][:N, :N] = lamA * np.eye(N)
    Ps, _ = kalman_path(I)
    R, Sig = recursion(I, Ps)
    Pic = np.ones((N, N)) / N; Pir = np.eye(N) - Pic
    pc = [1 / (1 / (s ** 2 + N * s_bar ** 2) + t / sig2) for t in range(T + 1)]
    pr = [1 / (1 / s ** 2 + t / sig2) for t in range(T + 1)]
    for t in range(T + 1):
        assert np.allclose(Ps[t][K:, K:], pc[t] * Pic + pr[t] * Pir, atol=1e-14), ("posterior", t)
    Ac, dc = scalar_recursion(lamA, gamma, sig2, pc, T); Ar, dr = scalar_recursion(lamA, gamma, sig2, pr, T)
    m = I["m0"] + 0.01 * rng.standard_normal(K + N)
    ells = []
    for t in range(T):
        G = R[t]["Gamma"][:N, :N]
        gc, gr = Ac[t] / lamA, Ar[t] / lamA
        assert np.allclose(G, gc * Pic + gr * Pir, atol=TOL), ("Gamma", t)
        assert np.allclose(R[t]["Gamma"][:N, N:], 0, atol=TOL) and np.allclose(R[t]["Gamma"][N:, N:], np.eye(2), atol=TOL)
        assert gc >= gr - 1e-15 and (abs(gc - gr) < 1e-12 if s_bar == 0 else gc > gr + 1e-9), ("speeds", t, gc, gr)
        # aim
        v = I["G"] @ m - I["eEc"] + I["rho"] * (R[t]["Cnext"] @ m + R[t]["cnext"])
        aim = np.linalg.solve(gamma * R[t]["Sigma"] + I["rho"] * R[t]["Anext"], v)
        alpha_hat = m[K:]
        wc, ellc, _ = ell_weights(lamA, gamma, sig2, pc, T, t); wr, ellr, _ = ell_weights(lamA, gamma, sig2, pr, T, t)
        assert abs(wc.sum() - 1) < 1e-12 and abs(wr.sum() - 1) < 1e-12 and wc.min() > 0 and wr.min() > 0
        aim_pred = (ellc * Pic + ellr * Pir) @ alpha_hat / (gamma * sig2)
        assert np.allclose(aim[:N], aim_pred, atol=1e-9), ("aim", t, aim[:N], aim_pred)
        for ell, p in [(ellc, pc[t]), (ellr, pr[t])]:
            assert sig2 / (sig2 + p) - 1e-12 <= ell <= 1 + 1e-12
        mark = (Pic / (gamma * (sig2 + pc[t])) + Pir / (gamma * (sig2 + pr[t]))) @ alpha_hat
        lf_c, lf_r = ellc * (sig2 + pc[t]) / sig2, ellr * (sig2 + pr[t]) / sig2
        assert lf_c >= 1 - 1e-12 and lf_r >= 1 - 1e-12
        assert np.allclose(aim[:N], (lf_c * Pic + lf_r * Pir) @ mark, atol=1e-9)
        # exposure myopic
        y_star = np.linalg.solve(gamma * (I["Sig_f"] + Ps[t][:K, :K]), m[:K])
        assert np.allclose(I["B"].T @ aim, y_star, atol=1e-9), ("exposure", t)
        ells.append((ellc, ellr, lf_c, lf_r))
    return ells, pc, pr


def main():
    for s_bar, gamma, T in itertools.product([0.0, 0.0035], [2.0, 5.0, 10.0], [4, 8]):
        ells, pc, pr = run(s_bar, gamma, T)
        print(f"  s_bar {s_bar:g} gamma {gamma:g} T {T}: two posterior variances and two speeds verified; "
              f"t=0 learning factors common {ells[0][2]:.3f}, relative {ells[0][3]:.3f}; ell common {ells[0][0]:.3f} <= relative {ells[0][1]:.3f}: {ells[0][0] <= ells[0][1] + 1e-12}")
        assert all(e[0] <= e[1] + 1e-12 for e in ells), "ell ordering observation failed"
    # observation: ell increases with lambda_A
    prev = None
    for lamA in [0.02, 0.05, 0.1, 0.2, 0.5]:
        ells, _, _ = run(0.0035, 5.0, 8, lamA=lamA)
        if prev is not None:
            assert ells[0][1] >= prev - 1e-12, ("ell not increasing in lambda_A", lamA)
        prev = ells[0][1]
        print(f"  lambda_A {lamA:g}: ell (relative direction, t=0) {ells[0][1]:.4f}")
    print("checks/032: all checks passed")


if __name__ == "__main__":
    main()
    sys.exit(0)
