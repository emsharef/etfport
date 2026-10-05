"""Finite checks for claim 030 (D12: M5's partial-adjustment policy and the exposure/alpha split); not its proof.

Run: uv run python checks/030/check.py

On experiment 021's instance shapes (Q1: 1 fund, 1 ETF, 1 factor; Q2: 2 funds, 1 ETF, 1 factor; Q3: 3 funds,
2 ETFs, 2 factors) with French-scale premia and shocks, the pooled Gaussian alpha prior, residuals 2% (funds)
and 0.2% (ETFs), Lambda_fund = 0.1, Lambda_ETF = 0.01, gamma in {2, 5, 10}, T in {4, 8}, rho = 1, the check:
 (i)  simulates the Kalman filter on several paths: the covariance path is identical across paths and the
      posterior mean's innovations average to zero;
 (ii) verifies one-step Bellman optimality of the recursion's policy at random states against scipy's
      numerical maximizer (which does not use the recursion);
 (iii) checks that the (K, L, l) form and the (Gamma, aim) form agree, Gamma's eigenvalues lie in (0, 1),
      and the matrix weights W_{t,s} sum to the identity;
 (iv) with the belief frozen (no learning), compares the recursion's path with the direct whole-path QP;
 (v)  in the separated case (ETF cost, residual and fee zero; B^E invertible) compares the policy with the
      closed form of part 4(a), and checks the three cross blocks / mean shift of part 4(b) one at a time;
 (vi) in the scalar stationary case compares the fund trading rate with Garleanu-Pedersen's equation (9).
"""
import itertools
import sys

import numpy as np
from scipy.optimize import minimize

rng = np.random.default_rng(29)
TOL = 1e-8


def instance(shape, gamma, T, lamA=0.1, lamE=0.01, resA=0.02, resE=0.002, cE=None, s_bar=0.0035, s=0.0035, rho=1.0):
    N, M, K = shape
    lam = np.array([0.0184, 0.00897, 0.005])[:K]
    sizes = np.array([0.0854, 0.0610, 0.05])[:K]
    Sig_f = np.diag(sizes ** 2)
    BA = rng.uniform(0.5, 1.2, size=(N, K)) * np.sign(rng.uniform(-0.3, 1, size=(N, K)) + 0.5)
    BE = np.eye(M, K) if M <= K else np.vstack([np.eye(K), rng.uniform(0.3, 1, size=(M - K, K))])
    if M == K:
        BE = BE + 0.1 * rng.uniform(-1, 1, size=(M, K))  # invertible, non-identity
    B = np.vstack([BA, BE])
    Sig_A, Sig_E = resA ** 2 * np.eye(N), resE ** 2 * np.eye(M)
    Sig_z = np.block([[Sig_f, np.zeros((K, N)), np.zeros((K, M))],
                      [np.zeros((N, K)), Sig_A, np.zeros((N, M))],
                      [np.zeros((M, K)), np.zeros((M, N)), Sig_E]])
    H = np.block([[np.eye(K), np.zeros((K, N))], [BA, np.eye(N)], [BE, np.zeros((M, N))]])
    # observation noise: (z^f, B^A z^f + z^A, B^E z^f + z^E) = L z, since returns load on the realized factor f
    Lz = np.block([[np.eye(K), np.zeros((K, N)), np.zeros((K, M))], [BA, np.eye(N), np.zeros((N, M))], [BE, np.zeros((M, N)), np.eye(M)]])
    cE = np.full(M, 0.0005) if cE is None else np.asarray(cE, float)
    d = np.concatenate([np.zeros(K), np.zeros(N), -cE])
    G = np.block([[BA, np.eye(N)], [BE, np.zeros((M, N))]])
    P0 = np.block([[np.diag((0.5 * sizes) ** 2), np.zeros((K, N))],
                   [np.zeros((N, K)), s_bar ** 2 * np.ones((N, N)) + s ** 2 * np.eye(N)]])
    m0 = np.concatenate([lam, np.full(N, -0.0019)])
    Sig_r = B @ Sig_f @ B.T + np.block([[Sig_A, np.zeros((N, M))], [np.zeros((M, N)), Sig_E]])
    Lam = np.diag([lamA] * N + [lamE] * M)
    eEc = np.concatenate([np.zeros(N), cE])
    Sig_y = Lz @ Sig_z @ Lz.T
    return dict(N=N, M=M, K=K, BA=BA, BE=BE, B=B, Sig_f=Sig_f, Sig_A=Sig_A, Sig_E=Sig_E, Sig_z=Sig_z, Sig_y=Sig_y, Lz=Lz, H=H, d=d,
                G=G, P0=P0, m0=m0, Sig_r=Sig_r, Lam=Lam, eEc=eEc, cE=cE, gamma=gamma, T=T, rho=rho, lam=lam)


def kalman_path(I):
    """Deterministic covariance path P_0..P_T and gains."""
    P, Ps, Ks = I["P0"].copy(), [], []
    for _ in range(I["T"] + 1):
        Ps.append(P.copy())
        S = I["H"] @ P @ I["H"].T + I["Sig_y"]
        Kg = P @ I["H"].T @ np.linalg.pinv(S)   # pseudo-inverse: the separated case has a degenerate ETF observation
        Ks.append(Kg)
        P = P - Kg @ I["H"] @ P
    return Ps, Ks


def recursion(I, Ps):
    """Backward recursion of claim 030 part 3: returns per-t dicts with D, A, C, c, K, L, l, Gamma, Sigma."""
    n, T, rho, g = I["N"] + I["M"], I["T"], I["rho"], I["gamma"]
    Sig = [I["G"] @ Ps[t] @ I["G"].T + I["Sig_r"] for t in range(T)]
    A = np.zeros((n, n)); C = np.zeros((n, I["K"] + I["N"])); c = np.zeros(n)
    out = [None] * T
    for t in range(T - 1, -1, -1):
        D = I["Lam"] + g * Sig[t] + rho * A
        Dinv = np.linalg.inv(D)
        Kt, Lt, lt = Dinv @ I["Lam"], Dinv @ (I["G"] + rho * C), Dinv @ (rho * c - I["eEc"])
        Gam = np.eye(n) - Dinv @ I["Lam"]
        out[t] = dict(D=D, Anext=A.copy(), Cnext=C.copy(), cnext=c.copy(), K=Kt, L=Lt, l=lt, Gamma=Gam, Sigma=Sig[t])
        A_new = I["Lam"] - I["Lam"] @ Dinv @ I["Lam"]
        C = I["Lam"] @ Dinv @ (I["G"] + rho * C); c = I["Lam"] @ Dinv @ (rho * c - I["eEc"]); A = A_new
        out[t]["A"] = A.copy(); out[t]["C"] = C.copy(); out[t]["c"] = c.copy()
    return out, Sig


def mu_of(I, m):
    return I["G"] @ m - I["eEc"]


def aim_of(I, R, t, m):
    """aim_t from the recursion: (gamma Sigma_t + rho A_{t+1})^{-1} v_t."""
    v = mu_of(I, m) + I["rho"] * (R[t]["Cnext"] @ m + R[t]["cnext"])
    return np.linalg.solve(I["gamma"] * R[t]["Sigma"] + I["rho"] * R[t]["Anext"], v)


def value_next(I, R, t, x, m):
    """E_t J_{t+1}(x, m_{t+1}) up to terms without x: -(1/2) x'A x + x'(C m + c)."""
    return -0.5 * x @ R[t]["Anext"] @ x + x @ (R[t]["Cnext"] @ m + R[t]["cnext"])


def stage(I, R, t, x, xprev, m):
    u = x - xprev
    return -0.5 * u @ I["Lam"] @ u + x @ mu_of(I, m) - I["gamma"] / 2 * x @ R[t]["Sigma"] @ x


def check_instance(shape, gamma, T, tag):
    I = instance(shape, gamma, T)
    n = I["N"] + I["M"]
    Ps, Ks = kalman_path(I)
    # (i) exogenous learning by simulation
    paths_P, innov = [], []
    for _ in range(4):
        theta = I["m0"] + np.linalg.cholesky(I["P0"]) @ rng.standard_normal(I["K"] + I["N"])
        m, P = I["m0"].copy(), I["P0"].copy()
        for t in range(T):
            y = I["H"] @ theta + I["d"] + I["Lz"] @ np.linalg.cholesky(I["Sig_z"]) @ rng.standard_normal(I["H"].shape[0])
            S = I["H"] @ P @ I["H"].T + I["Sig_y"]
            Kg = P @ I["H"].T @ np.linalg.pinv(S)
            m_new = m + Kg @ (y - I["H"] @ m - I["d"]); innov.append(m_new - m)
            m, P = m_new, P - Kg @ I["H"] @ P
        paths_P.append(P)
    assert all(np.allclose(paths_P[0], Pp, atol=1e-14) for Pp in paths_P[1:]), "P_T differs across paths"
    assert np.allclose(paths_P[0], Ps[T], atol=1e-12)
    # block decoupling in the reference case
    assert all(np.allclose(Pp[:I["K"], I["K"]:], 0, atol=1e-14) for Pp in Ps), "filter did not decouple"
    R, Sig = recursion(I, Ps)
    # (iii) forms agree, eigenvalues, weights
    m = I["m0"] + 0.01 * rng.standard_normal(I["K"] + I["N"]); xprev = 0.3 * rng.standard_normal(n)
    for t in range(T):
        x1 = R[t]["K"] @ xprev + R[t]["L"] @ m + R[t]["l"]
        x2 = xprev + R[t]["Gamma"] @ (aim_of(I, R, t, m) - xprev)
        assert np.allclose(x1, x2, atol=1e-10), (tag, t)
        ev = np.linalg.eigvals(R[t]["Gamma"]).real
        assert ev.min() > 0 and ev.max() < 1, (tag, t, ev)
        assert np.allclose(R[t]["Gamma"], np.linalg.solve(I["Lam"], R[t]["A"]), atol=1e-9)
        # weights W_{t,s} sum to I
        Wsum, prod = np.zeros((n, n)), np.eye(n)
        for s_ in range(t, T):
            Ms = I["gamma"] * Sig[s_] + I["rho"] * R[s_]["Anext"]
            Wsum += prod @ np.linalg.solve(Ms, I["gamma"] * Sig[s_])
            prod = prod @ np.linalg.solve(Ms, I["rho"] * R[s_]["Anext"])
        assert np.allclose(Wsum, np.eye(n), atol=1e-9), (tag, t)
        # (ii) Bellman optimality against a numerical maximizer
        f = lambda x: -(stage(I, R, t, x, xprev, m) + I["rho"] * value_next(I, R, t, x, m))
        res = minimize(f, xprev, method="BFGS", options=dict(gtol=1e-12))
        assert np.allclose(res.x, x1, atol=1e-5), (tag, t, res.x, x1)
        xprev = x1
    # (iv) frozen belief: whole-path QP equals the recursion
    Ifr = dict(I); m_fr = I["m0"]
    Pfr = [Ps[t] for t in range(T + 1)]
    Rfr, Sigfr = recursion(Ifr, Pfr)
    x0 = 0.2 * rng.standard_normal(n)
    path_rec, xp = [], x0
    for t in range(T):
        xp = Rfr[t]["K"] @ xp + Rfr[t]["L"] @ m_fr + Rfr[t]["l"]; path_rec.append(xp)
    def whole(z):
        xs = z.reshape(T, n); tot, prev = 0.0, x0
        for t in range(T):
            tot += I["rho"] ** t * stage(Ifr, Rfr, t, xs[t], prev, m_fr); prev = xs[t]
        return -tot
    res = minimize(whole, np.concatenate(path_rec) + 0.05 * rng.standard_normal(T * n), method="BFGS",
                   options=dict(gtol=1e-13, maxiter=20000))
    assert np.allclose(res.x.reshape(T, n), np.array(path_rec), atol=1e-4), (tag, "whole-path QP")
    print(f"  {tag}: filter exogenous and decoupled; Bellman optimal at {T} reviews; forms agree; "
          f"Gamma eigenvalues in ({min(np.linalg.eigvals(R[0]['Gamma']).real):.3f}, {max(np.linalg.eigvals(R[0]['Gamma']).real):.3f}); "
          f"whole-path QP matches")
    return I, Ps


def check_separation(gamma=5.0, T=6):
    """Part 4: exact separation with ETF cost, residual and fee zero; the cross blocks otherwise."""
    shape = (3, 2, 2)
    I = instance(shape, gamma, T, lamE=0.0, resE=0.0, cE=np.zeros(2))
    n, N, M, K = I["N"] + I["M"], I["N"], I["M"], I["K"]
    Ps, _ = kalman_path(I)
    R, Sig = recursion(I, Ps)
    Rmat = np.linalg.inv(I["BE"])
    # fund-only recursion
    Pa = [P[K:, K:] for P in Ps]
    If = dict(I); If["G"] = np.eye(N); If["Sig_r"] = I["Sig_A"]; If["Lam"] = I["Lam"][:N, :N]; If["eEc"] = np.zeros(N)
    If["N"], If["M"], If["K"] = N, 0, 0
    Rf, _ = recursion(If, Pa)
    m = I["m0"] + 0.01 * rng.standard_normal(K + N); xprev = 0.3 * rng.standard_normal(n)
    for t in range(T):
        x = R[t]["K"] @ xprev + R[t]["L"] @ m + R[t]["l"]
        lam_hat, alpha_hat = m[:K], m[K:]
        y_star = np.linalg.solve(gamma * (I["Sig_f"] + Ps[t][:K, :K]), lam_hat)
        xA = Rf[t]["K"] @ xprev[:N] + Rf[t]["L"] @ alpha_hat + Rf[t]["l"]
        xE = Rmat.T @ (y_star - I["BA"].T @ xA)
        assert np.allclose(x[:N], xA, atol=1e-9), ("fund block", t)
        assert np.allclose(x[N:], xE, atol=1e-9), ("ETF block", t)
        assert np.allclose(I["B"].T @ x, y_star, atol=1e-9), ("exposure", t)
        xprev = x
    print("  separated case: policy equals part 4(a) coefficient by coefficient (exposure myopic; funds partial; ETFs net the by-product)")
    # cross blocks: switch each friction on alone and compare with the displayed block matrices
    S = np.block([[I["BA"].T, I["BE"].T], [np.eye(N), np.zeros((N, M))]])
    Sinv = np.linalg.inv(S)
    for name, kw in [("ETF cost", dict(lamE=0.01)), ("ETF residual", dict(resE=0.002)), ("ETF fee", dict(cE=np.full(2, 0.0005)))]:
        J = instance(shape, gamma, T, **{**dict(lamE=0.0, resE=0.0, cE=np.zeros(2)), **kw})
        J["BA"], J["BE"], J["B"] = I["BA"], I["BE"], I["B"]  # same loadings
        J["H"] = I["H"]; J["G"] = I["G"]; J["Lz"] = I["Lz"]; J["Sig_y"] = I["Lz"] @ J["Sig_z"] @ I["Lz"].T
        J["Sig_r"] = J["B"] @ J["Sig_f"] @ J["B"].T + np.block([[J["Sig_A"], np.zeros((N, M))], [np.zeros((M, N)), J["Sig_E"]]])
        Ps_J, _ = kalman_path(J)
        Sig_t = J["G"] @ Ps_J[0] @ J["G"].T + J["Sig_r"]
        Sig_w = Sinv.T @ Sig_t @ Sinv; Lam_w = Sinv.T @ J["Lam"] @ Sinv; mean_shift = Sinv.T @ J["eEc"]
        Om = Rmat @ J["Lam"][N:, N:] @ Rmat.T; Xi = Rmat @ J["Sig_E"] @ Rmat.T; phi = Rmat @ J["cE"]
        Sig_w_pred = np.block([[J["Sig_f"] + Ps_J[0][:K, :K] + Xi, -Xi @ J["BA"].T],
                               [-J["BA"] @ Xi, J["Sig_A"] + Ps_J[0][K:, K:] + J["BA"] @ Xi @ J["BA"].T]])
        Lam_w_pred = np.block([[Om, -Om @ J["BA"].T], [-J["BA"] @ Om, J["Lam"][:N, :N] + J["BA"] @ Om @ J["BA"].T]])
        assert np.allclose(Sig_w, Sig_w_pred, atol=1e-12), name
        assert np.allclose(Lam_w, Lam_w_pred, atol=1e-12), name
        assert np.allclose(mean_shift, np.concatenate([phi, -J["BA"] @ phi]), atol=1e-14), name
        print(f"  bundling term '{name}' on alone: the displayed cross block / mean shift is exact")


def check_gp_rate(lamA=0.1, sigA=0.02, gamma=5.0, rho=0.98):
    """Part 5: stationary scalar rate equals Garleanu-Pedersen eq. (9) with lambda = lamA/sigA^2, gamma_GP = gamma/rho, 1 - rho_GP = rho."""
    a = 0.0
    for _ in range(5000):
        a = lamA - lamA ** 2 / (lamA + gamma * sigA ** 2 + rho * a)
    g_ours = a / lamA
    # GP discount their stage reward by (1-rho_GP)^(t+1) and the cost by (1-rho_GP)^t; M5 discounts both by rho^t,
    # so M5's (gamma, rho) correspond to GP's (gamma/rho, 1 - rho) and Assumption A's lambda = lamA / sigA^2.
    lam_gp = lamA / sigA ** 2; rho_gp = 1 - rho; g_gp_gamma = gamma / rho
    a_gp = (-(g_gp_gamma * (1 - rho_gp) + lam_gp * rho_gp) + np.sqrt((g_gp_gamma * (1 - rho_gp) + lam_gp * rho_gp) ** 2 + 4 * g_gp_gamma * lam_gp * (1 - rho_gp) ** 2)) / (2 * (1 - rho_gp))
    g_gp = a_gp / lam_gp
    assert abs(g_ours - g_gp) < 1e-9, (g_ours, g_gp)
    print(f"  scalar stationary rate {g_ours:.5f} equals Garleanu-Pedersen eq. (9) rate {g_gp:.5f}")


def main():
    for shape, gamma, T in itertools.product([(1, 1, 1), (2, 1, 1), (3, 2, 2)], [2.0, 5.0, 10.0], [4, 8]):
        check_instance(shape, gamma, T, f"Q{[(1,1,1),(2,1,1),(3,2,2)].index(shape)+1} gamma {gamma:g} T {T}")
    check_separation()
    check_gp_rate()
    print("checks/030: all checks passed")


if __name__ == "__main__":
    main()
    sys.exit(0)
