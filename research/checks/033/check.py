"""Finite checks for claim 033 (D14: value loss of M5's policy run with an estimated covariance); not its proof.

Run: uv run python checks/033/check.py

 (i)  small instance: the loss identity (part 1) against a Monte Carlo difference of realized objectives under common
      random numbers, and part 2's exact moment recursion against Monte Carlo second moments;
 (ii) part 3's non-local Riccati bounds on random perturbations of the covariance path, including large ones;
 (iii) experiment 022's calibration (registered loadings, fees, residual dispersions; French factor moments 1963Q3-2025Q2
      hard-coded from the analyst's instance): exact plug-in loss with the return covariance estimated from 160 quarters,
      the part 2 and part 3 bounds, as fractions of the optimal value and in bp per quarter.
"""
import os
import sys

import numpy as np

import importlib.util


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(os.path.dirname(__file__), "..", rel, "check.py"))
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod


_c30 = _load("check030", "030")
kalman_path, recursion, instance = _c30.kalman_path, _c30.recursion, _c30.instance
rng = np.random.default_rng(33)


# ---------- generic machinery on an instance dict I (checks/030 conventions) ----------
def coefs(I, Sig_path):
    """Claim 030's recursion with an arbitrary covariance path (list of Sigma_t)."""
    n, T, rho, g = I["N"] + I["M"], I["T"], I["rho"], I["gamma"]
    A = np.zeros((n, n)); C = np.zeros((n, I["K"] + I["N"])); c = np.zeros(n)
    out = [None] * T
    for t in range(T - 1, -1, -1):
        D = I["Lam"] + g * Sig_path[t] + rho * A
        Dinv = np.linalg.inv(D)
        out[t] = dict(D=D, A=A.copy(), K=Dinv @ I["Lam"], L=Dinv @ (I["G"] + rho * C), l=Dinv @ (rho * c - I["eEc"]))
        A_new = I["Lam"] - I["Lam"] @ Dinv @ I["Lam"]
        C = I["Lam"] @ Dinv @ (I["G"] + rho * C); c = I["Lam"] @ Dinv @ (rho * c - I["eEc"]); A = A_new
    return out


def innovation_covs(I, Ps, Ks):
    """V_t = K_t (H P_t H' + Sig_y) K_t'."""
    return [Ks[t] @ (I["H"] @ Ps[t] @ I["H"].T + I["Sig_y"]) @ Ks[t].T for t in range(I["T"])]


def exact_loss(I, Sig_true, Rt, Rp, x0, m0, V):
    """Part 2: (1/2) sum rho^t tr(D_t E[e e']) by the exact moment recursion of z = (x_{t-1}, m_t) under the plug-in rule."""
    n, d, T, rho = I["N"] + I["M"], I["K"] + I["N"], I["T"], I["rho"]
    mu = np.concatenate([x0, m0]); S = np.outer(mu, mu)
    loss = 0.0
    for t in range(T):
        dK, dL, dl = Rp[t]["K"] - Rt[t]["K"], Rp[t]["L"] - Rt[t]["L"], Rp[t]["l"] - Rt[t]["l"]
        Mz = np.hstack([dK, dL])
        Eee = Mz @ S @ Mz.T + np.outer(Mz @ mu, dl) + np.outer(dl, Mz @ mu) + np.outer(dl, dl)
        loss += rho ** t * 0.5 * np.trace(Rt[t]["D"] @ Eee)
        F = np.zeros((n + d, n + d)); F[:n, :n] = Rp[t]["K"]; F[:n, n:] = Rp[t]["L"]; F[n:, n:] = np.eye(d)
        f = np.concatenate([Rp[t]["l"], np.zeros(d)])
        W = np.zeros((n + d, n + d)); W[n:, n:] = V[t]
        S = F @ S @ F.T + np.outer(F @ mu, f) + np.outer(f, F @ mu) + np.outer(f, f) + W
        mu = F @ mu + f
    return loss


def simulate_values(I, Sig_true, Rt, Rp, x0, m0, V, paths=4000):
    """Monte Carlo: realized objective of the true and plug-in policies under common random numbers, and E[e e'] at t=0..."""
    n, d, T, rho, g = I["N"] + I["M"], I["K"] + I["N"], I["T"], I["rho"], I["gamma"]
    chol = [np.linalg.cholesky(V[t] + 1e-18 * np.eye(d)) for t in range(T)]
    vt = np.zeros(paths); vp = np.zeros(paths); ident = np.zeros(paths)
    for r in range(paths):
        m = m0.copy(); xt = x0.copy(); xp = x0.copy()
        for t in range(T):
            mu = I["G"] @ m - I["eEc"]
            xt_new = Rt[t]["K"] @ xt + Rt[t]["L"] @ m + Rt[t]["l"]
            xp_new = Rp[t]["K"] @ xp + Rp[t]["L"] @ m + Rp[t]["l"]
            for x_new, x_old, acc in ((xt_new, xt, vt), (xp_new, xp, vp)):
                u = x_new - x_old
                acc[r] += rho ** t * (x_new @ mu - g / 2 * x_new @ Sig_true[t] @ x_new - 0.5 * u @ I["Lam"] @ u)
            e = xp_new - (Rt[t]["K"] @ xp + Rt[t]["L"] @ m + Rt[t]["l"])
            ident[r] += rho ** t * 0.5 * e @ Rt[t]["D"] @ e
            xt, xp = xt_new, xp_new
            m = m + chol[t] @ rng.standard_normal(d)
    return vt.mean(), vp.mean(), ident.mean(), (vt - vp).std() / np.sqrt(paths), ident.std() / np.sqrt(paths)


def star_norm(Y, Lam_inv_half):
    return np.linalg.norm(Lam_inv_half @ Y @ Lam_inv_half, 2)


def part3_bounds(I, Sig_true, Sig_est, Rt, Rp):
    """Verify ||delta M_t|| <= sum rho^{s-t} gamma ||dSigma_s||_* and the K, L, l bounds."""
    n, T, rho, g = I["N"] + I["M"], I["T"], I["rho"], I["gamma"]
    Lh = np.linalg.cholesky(I["Lam"]); Lam_half = Lh @ Lh.T  # symmetric sqrt via eig instead
    w, U = np.linalg.eigh(I["Lam"]); Lam_half = U @ np.diag(np.sqrt(w)) @ U.T; Lam_ih = U @ np.diag(1 / np.sqrt(w)) @ U.T
    dS = [star_norm(Sig_est[t] - Sig_true[t], Lam_ih) for t in range(T)]
    gG = np.linalg.norm(Lam_ih @ I["G"], 2); eE = np.linalg.norm(Lam_ih @ I["eEc"])
    dM_bound = [sum(rho ** (s - t) * g * dS[s] for s in range(t, T)) for t in range(T)]
    ok = True
    for t in range(T):
        dM = np.linalg.norm(Lam_ih @ (Rp[t]["A"] - Rt[t]["A"]) @ Lam_ih, 2)
        dK = np.linalg.norm(Lam_half @ (Rp[t]["K"] - Rt[t]["K"]) @ Lam_ih, 2)
        dR_bound = [g * dS[s] + (rho * dM_bound[s + 1] if s + 1 < T else 0.0) for s in range(T)]
        dL = np.linalg.norm(Lam_half @ (Rp[t]["L"] - Rt[t]["L"]), 2)
        dl = np.linalg.norm(Lam_half @ (Rp[t]["l"] - Rt[t]["l"]))
        L_bound = sum(rho ** (s - t) * dR_bound[s] * gG * (T - s) for s in range(t, T))
        l_bound = sum(rho ** (s - t) * dR_bound[s] * eE * (T - s) for s in range(t, T))
        ok &= dM <= dM_bound[t] + 1e-12 and dK <= dR_bound[t] + 1e-12 and dL <= L_bound + 1e-9 and dl <= l_bound + 1e-9
        assert ok, (t, dM, dM_bound[t], dK, dR_bound[t], dL, L_bound, dl, l_bound)
    return dM_bound


def part2_bound(I, Rt, Rp, x0, m0, V):
    """The displayed loss bound from the state moments under the plug-in rule."""
    n, d, T, rho = I["N"] + I["M"], I["K"] + I["N"], I["T"], I["rho"]
    w, U = np.linalg.eigh(I["Lam"]); Lam_half = U @ np.diag(np.sqrt(w)) @ U.T; Lam_ih = U @ np.diag(1 / np.sqrt(w)) @ U.T
    mu = np.concatenate([x0, m0]); S = np.outer(mu, mu); total = 0.0
    for t in range(T):
        rx = np.sqrt(np.trace(Lam_half @ S[:n, :n] @ Lam_half)); rm = np.sqrt(np.trace(S[n:, n:]))
        dK = np.linalg.norm(Lam_half @ (Rp[t]["K"] - Rt[t]["K"]) @ Lam_ih, 2)
        dL = np.linalg.norm(Lam_half @ (Rp[t]["L"] - Rt[t]["L"]), 2); dl = np.linalg.norm(Lam_half @ (Rp[t]["l"] - Rt[t]["l"]))
        Dstar = np.linalg.norm(Lam_ih @ Rt[t]["D"] @ Lam_ih, 2)
        total += rho ** t * 0.5 * Dstar * (dK * rx + dL * rm + dl) ** 2
        F = np.zeros((n + d, n + d)); F[:n, :n] = Rp[t]["K"]; F[:n, n:] = Rp[t]["L"]; F[n:, n:] = np.eye(d)
        f = np.concatenate([Rp[t]["l"], np.zeros(d)]); W = np.zeros((n + d, n + d)); W[n:, n:] = V[t]
        S = F @ S @ F.T + np.outer(F @ mu, f) + np.outer(f, F @ mu) + np.outer(f, f) + W; mu = F @ mu + f
    return total


def optimal_value(I, Sig_true, Rt, x0, m0, V, paths=4000):
    vt = simulate_values(I, Sig_true, Rt, Rt, x0, m0, V, paths)[0]
    return vt


# ---------- (i)-(ii): small instance ----------
def small_checks():
    I = instance((2, 2, 2), 5.0, 6)
    Ps, Ks = kalman_path(I)
    Sig_true = [I["G"] @ Ps[t] @ I["G"].T + I["Sig_r"] for t in range(I["T"])]
    V = innovation_covs(I, Ps, Ks)
    Rt = coefs(I, Sig_true)
    x0 = 0.2 * np.ones(I["N"] + I["M"]); m0 = I["m0"]
    for scale, label in [(0.3, "moderate"), (2.0, "large")]:
        E = rng.standard_normal(I["Sig_r"].shape); E = scale * (E @ E.T) / E.shape[0] * np.trace(I["Sig_r"]) / E.shape[0]
        Sig_est = [S + E for S in Sig_true]
        Rp = coefs(I, Sig_est)
        loss = exact_loss(I, Sig_true, Rt, Rp, x0, m0, V)
        vt, vp, ident, se, se_i = simulate_values(I, Sig_true, Rt, Rp, x0, m0, V, paths=3000)
        assert abs(ident - loss) < 4 * se_i + 1e-9, ("identity vs exact recursion", ident, loss, se_i)
        assert abs((vt - vp) - loss) < 4 * se + 1e-9, ("Monte Carlo difference vs identity", vt - vp, loss, se)
        part3_bounds(I, Sig_true, Sig_est, Rt, Rp)
        b2 = part2_bound(I, Rt, Rp, x0, m0, V)
        assert loss <= b2 + 1e-12
        print(f"  small instance, {label} covariance error: MC value gap {(vt - vp):.4e} (SE {se:.1e}) = identity {ident:.4e} = exact recursion {loss:.4e}; "
              f"part 2 bound {b2:.3e}; part 3 bounds hold")


# ---------- (iii): experiment 022's calibration ----------
LAM = np.array([0.01839731220421369, 0.005486247409201608, 0.008970078500483867, 0.00837681205265322, 0.0077187195079677345])
SF = np.array([[0.007290426159522208, 0.0019382246396524299, -0.0013233091840916956, -0.000763166083745376, -0.0013435205872932045],
               [0.0019382246396524299, 0.0030826838903637087, 0.0002928132157484199, -0.00039455268329907753, -0.00018626180568308355],
               [-0.0013233091840916956, 0.0002928132157484199, 0.003715343030870247, 0.00022455855226105823, 0.0018676825784110923],
               [-0.000763166083745376, -0.00039455268329907753, 0.00022455855226105823, 0.001772087114311297, 0.00010948627892568625],
               [-0.0013435205872932045, -0.00018626180568308355, 0.0018676825784110923, 0.00010948627892568625, 0.001741958851287992]])
NQ = 248
ETF_B = np.array([[1, 0, 0, 0, 0], [1, 0.8, 0.2, 0, 0], [1, 0, 0.6, 0, 0], [1, 0, -0.4, 0, 0],
                  [1, 0, 0, 0.4, 0], [1, 0, 0, 0, 0.4], [1, 0.8, 0.6, 0, 0], [1, 0.3, 0.1, 0, 0]], float)
ETF_FEE = np.array([1, 4, 4, 4, 5, 5, 5, 5]) * 1e-4


def exp022_instance(gamma=5.0, T=40, lamA=0.1, lamE=0.01):
    """Experiment 022's registered instance in checks/030 conventions (theta = (lambda, alpha) order)."""
    r = np.random.default_rng(2022)
    N, M, K = 30, 8, 5
    beta = r.uniform(0.85, 1.15, N); tilts = r.normal(0, 0.3, (N, 4)); BA = np.column_stack([beta, tilts])
    sdA = r.uniform(0.01, 0.03, N)
    BE = ETF_B; B = np.vstack([BA, BE])
    Sig_A = np.diag(sdA ** 2); Sig_E = 0.003 ** 2 * np.eye(M)
    Sig_z = np.block([[SF, np.zeros((K, N)), np.zeros((K, M))], [np.zeros((N, K)), Sig_A, np.zeros((N, M))], [np.zeros((M, K)), np.zeros((M, N)), Sig_E]])
    H = np.block([[np.eye(K), np.zeros((K, N))], [BA, np.eye(N)], [BE, np.zeros((M, N))]])
    Lz = np.block([[np.eye(K), np.zeros((K, N)), np.zeros((K, M))], [BA, np.eye(N), np.zeros((N, M))], [BE, np.zeros((M, N)), np.eye(M)]])
    G = np.block([[BA, np.eye(N)], [BE, np.zeros((M, N))]])
    s_bar = 0.0025 / 4; s2 = 0.0035 ** 2 - s_bar ** 2
    P0 = np.block([[SF / NQ, np.zeros((K, N))], [np.zeros((N, K)), s_bar ** 2 * np.ones((N, N)) + s2 * np.eye(N)]])
    m0 = np.concatenate([LAM, np.full(N, -0.0019)])
    Sig_r = B @ SF @ B.T + np.block([[Sig_A, np.zeros((N, M))], [np.zeros((M, N)), Sig_E]])
    Lam = np.diag([lamA] * N + [lamE] * M)
    return dict(N=N, M=M, K=K, BA=BA, BE=BE, B=B, Sig_f=SF, Sig_A=Sig_A, Sig_E=Sig_E, Sig_z=Sig_z, Sig_y=Lz @ Sig_z @ Lz.T, Lz=Lz, H=H,
                d=np.concatenate([np.zeros(K + N), -ETF_FEE]), G=G, P0=P0, m0=m0, Sig_r=Sig_r, Lam=Lam,
                eEc=np.concatenate([np.zeros(N), ETF_FEE]), cE=ETF_FEE, gamma=gamma, T=T, rho=1.0, lam=LAM, sdA=sdA)


def calibrated(n_hist=160, draws=5):
    I = exp022_instance()
    N, M, K, T = I["N"], I["M"], I["K"], I["T"]
    Ps, Ks = kalman_path(I)
    Sig_true = [I["G"] @ Ps[t] @ I["G"].T + I["Sig_r"] for t in range(T)]
    V = innovation_covs(I, Ps, Ks)
    Rt = coefs(I, Sig_true)
    x0 = np.concatenate([np.full(N, 0.5 / N), [0.5], np.zeros(M - 1)]); m0 = I["m0"]
    Vstar = optimal_value(I, Sig_true, Rt, x0, m0, V, paths=400)
    # gross position of the optimal policy at t=0 (scale of the problem)
    x1 = Rt[0]["K"] @ x0 + Rt[0]["L"] @ m0 + Rt[0]["l"]
    print(f"  experiment 022 calibration: optimal value ~ {Vstar / T * 1e4:.1f} bp per quarter (MC, 400 paths); gross position at t=0 {np.abs(x1).sum():.1f}")
    Lf = np.linalg.cholesky(SF)
    for k in range(draws):
        # sample covariance from n_hist quarters: factor block Wishart, residual variances chi-square
        Z = Lf @ rng.standard_normal((K, n_hist)); Sf_hat = Z @ Z.T / n_hist
        sdA_hat2 = I["sdA"] ** 2 * rng.chisquare(n_hist - 1, N) / (n_hist - 1)
        sdE_hat2 = 0.003 ** 2 * rng.chisquare(n_hist - 1, M) / (n_hist - 1)
        Sig_r_hat = I["B"] @ Sf_hat @ I["B"].T + np.diag(np.concatenate([sdA_hat2, sdE_hat2]))
        Sig_est = [I["G"] @ Ps[t] @ I["G"].T + Sig_r_hat for t in range(T)]
        Rp = coefs(I, Sig_est)
        loss = exact_loss(I, Sig_true, Rt, Rp, x0, m0, V)
        b2 = part2_bound(I, Rt, Rp, x0, m0, V)
        dMb = part3_bounds(I, Sig_true, Sig_est, Rt, Rp)
        rel = np.linalg.norm(Sf_hat - SF, 2) / np.linalg.norm(SF, 2)
        print(f"  draw {k + 1}: factor-covariance error {rel * 100:.1f}% (spectral, relative); exact plug-in loss {loss / T * 1e4:.3f} bp per quarter "
              f"= {loss / Vstar * 100:.2f}% of the optimum; part 2 bound {b2 / T * 1e4:.1f} bp per quarter ({b2 / max(loss, 1e-300):.0f}x the loss); "
              f"part 3 coefficient bound ||delta M_0|| <= {dMb[0]:.3f}")
        assert loss >= -1e-9 and loss <= b2 + 1e-9


def main():
    small_checks()
    calibrated()
    print("checks/033: all checks passed")


if __name__ == "__main__":
    main()
    sys.exit(0)
