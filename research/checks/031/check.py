"""Finite checks for claim 031 (D12: the missing-direction leak of premium beliefs into fund choice); not its proof.

Run: uv run python checks/031/check.py

With ETF frictions off (Lambda_E = 0, Sigma_E = 0, c^E = 0), on instances with 2 funds, 1 ETF, 2 factors
(missing direction) and 3 funds, 2 ETFs, 2 factors (spanning control), the check:
 (a) compares claim 030's full recursion (original coordinates) with claim 031's exposure rule (part 2)
     plus the reduced fund recursion (part 3), coefficient by coefficient at every review;
 (b) compares the fund policy's sensitivity to lambda_hat with the reduced recursion's L^A_t B^A J_t';
 (c) verifies the leak vanishes when the fund loadings lie in the ETF span and is nonzero otherwise;
 (d) checks the Schur complement decreases along the Kalman path;
 (e) with correlated factors, verifies the hedge term against a direct minimum-variance regression.
"""
import os
import sys

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "030"))
from check import instance, kalman_path, recursion, rng  # noqa: E402

TOL = 1e-9


def projections(BE):
    """Orthogonal projections onto row(B^E) and its complement, and the left inverse of B^E'."""
    K = BE.shape[1]
    Q, _ = np.linalg.qr(BE.T)                     # K x M orthonormal basis of L_E
    PiR = Q @ Q.T; PiU = np.eye(K) - PiR
    BEt_plus = np.linalg.solve(BE @ BE.T, BE)     # (B^E')^+ = (B^E B^E')^{-1} B^E
    return PiR, PiU, BEt_plus


def reduced(I, Ps):
    """Part 3's reduced fund moments per review, and the hedge map J_t."""
    K, N = I["K"], I["N"]
    PiR, PiU, _ = projections(I["BE"])
    out = []
    for t in range(I["T"]):
        St = I["Sig_f"] + Ps[t][:K, :K]
        SRR, SRU, SUU = PiR @ St @ PiR, PiR @ St @ PiU, PiU @ St @ PiU
        SRR_inv = np.linalg.pinv(SRR)             # inverse on L_E
        schur = SUU - SRU.T @ SRR_inv @ SRU
        J = PiU - PiR @ SRR_inv @ SRU             # J_t; J_t' = PiU - SUR SRR^{-1} PiR
        Sig_red = I["Sig_A"] + Ps[t][K:, K:] + I["BA"] @ schur @ I["BA"].T
        out.append(dict(St=St, SRR_inv=SRR_inv, SRU=SRU, schur=schur, J=J, Sig_red=Sig_red))
    return out


def fund_recursion(I, red):
    """Claim 030's recursion for the fund block with mean alpha^red_t = alpha_hat + B^A J_t' lambda_hat."""
    N, K, T, rho, g = I["N"], I["K"], I["T"], I["rho"], I["gamma"]
    LamA = I["Lam"][:N, :N]
    # mean map from m = (lambda_hat, alpha_hat): alpha^red = Gm_t m with Gm_t = [B^A J_t', I]
    Gm = [np.hstack([I["BA"] @ red[t]["J"].T, np.eye(N)]) for t in range(T)]
    A = np.zeros((N, N)); C = np.zeros((N, K + N)); c = np.zeros(N)
    out = [None] * T
    for t in range(T - 1, -1, -1):
        D = LamA + g * red[t]["Sig_red"] + rho * A
        Dinv = np.linalg.inv(D)
        out[t] = dict(K=Dinv @ LamA, L=Dinv @ (Gm[t] + rho * C), l=Dinv @ (rho * c))
        A_new = LamA - LamA @ Dinv @ LamA
        C = LamA @ Dinv @ (Gm[t] + rho * C); c = LamA @ Dinv @ (rho * c); A = A_new
    return out


def make(shape, gamma, T, replicable=False, corr=0.0):
    I = instance(shape, gamma, T, lamE=0.0, resE=0.0, cE=np.zeros(shape[1]))
    N, M, K = shape
    if corr:
        sizes = np.sqrt(np.diag(I["Sig_f"]))
        Sf = np.outer(sizes, sizes) * (np.full((K, K), corr) + (1 - corr) * np.eye(K))
        I["Sig_f"] = Sf
        I["Sig_z"][:K, :K] = Sf
    if replicable:
        # move every fund loading into the ETF span
        PiR, _, _ = projections(I["BE"])
        I["BA"] = I["BA"] @ PiR
    I["B"] = np.vstack([I["BA"], I["BE"]])
    I["H"] = np.block([[np.eye(K), np.zeros((K, N))], [I["BA"], np.eye(N)], [I["BE"], np.zeros((M, N))]])
    I["G"] = np.block([[I["BA"], np.eye(N)], [I["BE"], np.zeros((M, N))]])
    I["Lz"] = np.block([[np.eye(K), np.zeros((K, N)), np.zeros((K, M))], [I["BA"], np.eye(N), np.zeros((N, M))], [I["BE"], np.zeros((M, N)), np.eye(M)]])
    I["Sig_y"] = I["Lz"] @ I["Sig_z"] @ I["Lz"].T
    I["Sig_r"] = I["B"] @ I["Sig_f"] @ I["B"].T + np.block([[I["Sig_A"], np.zeros((N, M))], [np.zeros((M, N)), I["Sig_E"]]])
    return I


def compare(I, tag):
    N, M, K, T = I["N"], I["M"], I["K"], I["T"]
    Ps, _ = kalman_path(I)
    R, _ = recursion(I, Ps)
    red = reduced(I, Ps)
    Rf = fund_recursion(I, red)
    PiR, PiU, BEt_plus = projections(I["BE"])
    m = I["m0"] + 0.01 * rng.standard_normal(K + N); xprev = 0.3 * rng.standard_normal(N + M)
    for t in range(T):
        x_full = R[t]["K"] @ xprev + R[t]["L"] @ m + R[t]["l"]
        xA = Rf[t]["K"] @ xprev[:N] + Rf[t]["L"] @ m + Rf[t]["l"]
        lam_hat = m[:K]
        yR = red[t]["SRR_inv"] @ (PiR @ lam_hat / I["gamma"] - red[t]["SRU"] @ I["BA"].T @ xA)
        xE = BEt_plus @ (yR - PiR @ I["BA"].T @ xA)
        assert np.allclose(x_full[:N], xA, atol=TOL), (tag, t, "fund block")
        assert np.allclose(x_full[N:], xE, atol=TOL), (tag, t, "ETF block")
        # (b) sensitivity to lambda_hat: the full L_t's lambda columns on the fund rows equal the reduced L^A_t's
        assert np.allclose(R[t]["L"][:N, :K], Rf[t]["L"][:, :K], atol=TOL), (tag, t, "lambda sensitivity")
        xprev = x_full
    # (d) Schur complement decreases along the path (Loewner order)
    for t in range(T - 1):
        ev = np.linalg.eigvalsh(red[t]["schur"] - red[t + 1]["schur"])
        assert ev.min() > -1e-12, (tag, t, "Schur not decreasing")
    leak = max(np.abs(Rf[t]["L"][:, :K]).max() for t in range(T))
    return leak, red


def main():
    for shape in [(2, 1, 2), (3, 2, 2)]:
        for gamma, T in [(5.0, 4), (2.0, 8)]:
            leak, red = compare(make(shape, gamma, T), f"{shape} gamma {gamma:g} T {T}")
            spanning = shape[1] >= shape[2]
            if spanning:
                assert leak < 1e-9, ("spanning shape leaks", leak)
            else:
                assert leak > 1e-6, ("missing direction does not leak", leak)
            print(f"  shape {shape} gamma {gamma:g} T {T}: full policy = exposure rule + reduced fund recursion; "
                  f"lambda-sensitivity of fund policy max {leak:.4f} ({'spanning: none' if spanning else 'missing direction: leak'})")
    # (c) replicable loadings in the missing-direction shape: the leak vanishes
    leak_rep, _ = compare(make((2, 1, 2), 5.0, 4, replicable=True), "replicable")
    assert leak_rep < 1e-9, leak_rep
    print(f"  (2,1,2) with fund loadings moved into the ETF span: lambda-sensitivity {leak_rep:.2e} (leak vanishes)")
    # (e) correlated factors: the hedge term equals the minimum-variance regression coefficient
    I = make((2, 1, 2), 5.0, 4, corr=0.4)
    Ps, _ = kalman_path(I); red = reduced(I, Ps)
    PiR, PiU, _ = projections(I["BE"])
    xA = rng.standard_normal(2)
    u = PiU @ I["BA"].T @ xA                       # unreachable exposure carried by the funds
    hedge = -red[0]["SRR_inv"] @ red[0]["SRU"] @ I["BA"].T @ xA
    # direct: minimize Var(y_R + u) over y_R in L_E => y_R = -SRR^{-1} SRU u (on L_E); compare via projection basis
    Q, _ = np.linalg.qr(I["BE"].T)
    Svv = Q.T @ red[0]["St"] @ Q; Svu = Q.T @ red[0]["St"] @ u
    hedge_direct = -Q @ np.linalg.solve(Svv, Svu)
    assert np.allclose(hedge, hedge_direct, atol=1e-12)
    leak_c, _ = compare(I, "correlated factors")
    print(f"  correlated factors: the ETF exposure's hedge of the funds' unreachable exposure equals the minimum-variance regression; leak {leak_c:.4f}")
    print("checks/031: all checks passed")


if __name__ == "__main__":
    main()
    sys.exit(0)
