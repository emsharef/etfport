"""Finite checks for claim 035 (D14: expected-loss guarantee under re-estimation); not its proof.

Run: uv run python checks/035/check.py

Small M5 instance; a manager re-estimates the return covariance at every review from a pre-sample plus the run's own
returns (sample covariances, positive semidefinite) and recomputes claim 030's coefficients:
 (i)  the loss identity holds in expectation against the realized objective difference (common random numbers;
      pathwise the telescoping leaves martingale differences);
 (ii) the a priori coefficient bounds of part 2 hold on every path and review, also with a tiny pre-sample;
 (iii) the position bound X_t and the on-event / off-event inequalities of parts 3-4 hold pathwise, and the guarantee's
      two terms bound the Monte Carlo expected loss.
Inputs are illustrative (rule 22).
"""
import importlib.util
import os
import sys

import numpy as np


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(os.path.dirname(__file__), "..", rel, "check.py"))
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod


_c30 = _load("check030", "030"); _c33 = _load("check033", "033")
kalman_path, instance = _c30.kalman_path, _c30.instance
coefs, innovation_covs = _c33.coefs, _c33.innovation_covs
rng = np.random.default_rng(35)


def lam_norms(I):
    w, U = np.linalg.eigh(I["Lam"]); return U @ np.diag(np.sqrt(w)) @ U.T, U @ np.diag(1 / np.sqrt(w)) @ U.T


def bounds_for_radius(I, Rt, r):
    """Claim 033 part 3 bounds with a constant error r on every review (bK, bL, bl per t) and 1 + ||R_t||."""
    T, rho, g = I["T"], I["rho"], I["gamma"]
    Lh, Lih = lam_norms(I)
    gG = np.linalg.norm(Lih @ I["G"], 2); eE = np.linalg.norm(Lih @ I["eEc"])
    dM = [sum(rho ** (s - t) * g * r for s in range(t, T)) for t in range(T)] + [0.0]
    bR = [g * r + rho * dM[t + 1] for t in range(T)]
    bK = bR
    bL = [sum(rho ** (s - t) * bR[s] * gG * (T - s) for s in range(t, T)) for t in range(T)]
    bl = [sum(rho ** (s - t) * bR[s] * eE * (T - s) for s in range(t, T)) for t in range(T)]
    oneR = [np.linalg.norm(Lih @ Rt[t]["D"] @ Lih, 2) for t in range(T)]
    return bK, bL, bl, oneR, gG, eE


def simulate(I, n0, paths, Rt, Sig_true, V, x0, m0):
    """Re-estimating manager: returns per-path realized loss identity, objective difference, coefficient checks."""
    n, d, T, rho, g = I["N"] + I["M"], I["K"] + I["N"], I["T"], I["rho"], I["gamma"]
    Lh, Lih = lam_norms(I)
    gG = np.linalg.norm(Lih @ I["G"], 2); eE = np.linalg.norm(Lih @ I["eEc"])
    chol_m = [np.linalg.cholesky(V[t] + 1e-18 * np.eye(d)) for t in range(T)]
    chol_r = np.linalg.cholesky(I["Sig_r"])
    out = []
    for _ in range(paths):
        # pre-sample of returns (excess of their mean; the covariance estimate is the sample covariance)
        hist = (chol_r @ rng.standard_normal((n, n0))).T
        m = m0.copy(); xt = x0.copy(); xp = x0.copy(); vt = vp = ident = 0.0
        deltas = []; Mstar = np.linalg.norm(m); Xbound_ok = True; coef_ok = True
        Xb = np.linalg.norm(Lh @ x0)
        for t in range(T):
            S_hat = np.cov(hist.T, bias=False) if hist.shape[0] > 1 else np.zeros((n, n))
            S_hat = 0.5 * (S_hat + S_hat.T)
            Sig_est = [I["G"] @ Ps_t @ I["G"].T + S_hat for Ps_t in PS_GLOBAL[t:T]]
            # recursion from t to T-1 with the current estimate (a shifted instance)
            Rp = coefs_from(I, Sig_est, t)
            deltas.append(np.linalg.norm(Lih @ (S_hat - I["Sig_r"]) @ Lih, 2))
            Kt, Lt, lt = Rp["K"], Rp["L"], Rp["l"]
            coef_ok &= np.linalg.norm(Lh @ Kt @ Lih, 2) <= 1 + 1e-9 and np.linalg.norm(Lh @ Lt, 2) <= gG * (T - t) + 1e-9 and np.linalg.norm(Lh @ lt) <= eE * (T - t) + 1e-9
            mu = I["G"] @ m - I["eEc"]
            xt_new = Rt[t]["K"] @ xt + Rt[t]["L"] @ m + Rt[t]["l"]
            xp_new = Kt @ xp + Lt @ m + lt
            for x_new, x_old, which in ((xt_new, xt, "t"), (xp_new, xp, "p")):
                u = x_new - x_old
                val = rho ** t * (x_new @ mu - g / 2 * x_new @ Sig_true[t] @ x_new - 0.5 * u @ I["Lam"] @ u)
                if which == "t": vt += val
                else: vp += val
            e = xp_new - (Rt[t]["K"] @ xp + Rt[t]["L"] @ m + Rt[t]["l"])
            ident += rho ** t * 0.5 * e @ Rt[t]["D"] @ e
            xt, xp = xt_new, xp_new
            Xb = Xb + gG * (T - t) * Mstar + eE * (T - t)   # part 2's bound uses M* (sup over the path); conservative to use running sup
            Xbound_ok &= np.linalg.norm(Lh @ xp) <= Xb + 1e-9
            # observe this quarter's return; update the belief and the history
            eta = chol_m[t] @ rng.standard_normal(d)
            r_obs = chol_r @ rng.standard_normal(n) + mu   # the history's returns are drawn from the return law, independently of the belief innovation; the inequalities checked do not depend on that coupling
            hist = np.vstack([hist, r_obs - mu])
            m = m + eta; Mstar = max(Mstar, np.linalg.norm(m))
        out.append(dict(vt=vt, vp=vp, ident=ident, deltas=deltas, coef_ok=coef_ok, X_ok=Xbound_ok, Mstar=Mstar))
    return out


PS_GLOBAL = None


def coefs_from(I, Sig_path_tail, t0):
    """Coefficients at review t0 from the recursion over s = t0..T-1 with the given path (list starting at t0)."""
    n, T, rho, g = I["N"] + I["M"], I["T"], I["rho"], I["gamma"]
    A = np.zeros((n, n)); C = np.zeros((n, I["K"] + I["N"])); c = np.zeros(n)
    for s in range(T - 1, t0 - 1, -1):
        D = I["Lam"] + g * Sig_path_tail[s - t0] + rho * A
        Dinv = np.linalg.inv(D)
        K, L, l = Dinv @ I["Lam"], Dinv @ (I["G"] + rho * C), Dinv @ (rho * c - I["eEc"])
        A_new = I["Lam"] - I["Lam"] @ Dinv @ I["Lam"]
        C = I["Lam"] @ Dinv @ (I["G"] + rho * C); c = I["Lam"] @ Dinv @ (rho * c - I["eEc"]); A = A_new
    return dict(K=K, L=L, l=l)


def main():
    global PS_GLOBAL
    I = instance((2, 2, 2), 5.0, 5)
    Ps, Ks = kalman_path(I); PS_GLOBAL = Ps
    Sig_true = [I["G"] @ Ps[t] @ I["G"].T + I["Sig_r"] for t in range(I["T"])]
    V = innovation_covs(I, Ps, Ks); Rt = coefs(I, Sig_true)
    x0 = 0.2 * np.ones(I["N"] + I["M"]); m0 = I["m0"]
    for n0 in (3, 40):
        out = simulate(I, n0, 300, Rt, Sig_true, V, x0, m0)
        # (i) identity pathwise
        gaps = np.array([o["vt"] - o["vp"] for o in out]); idents = np.array([o["ident"] for o in out])
        # the identity is an equality of expectations (the telescoping leaves martingale differences pathwise)
        se = np.sqrt(gaps.var() / len(gaps) + idents.var() / len(idents))
        assert abs(gaps.mean() - idents.mean()) < 4 * se + 1e-9, (gaps.mean(), idents.mean(), se)
        # (ii) a priori bounds and (iii) position bound
        assert all(o["coef_ok"] for o in out) and all(o["X_ok"] for o in out)
        # on/off decomposition with an event defined by realized radii: r_t = 90th percentile of delta_t over paths
        deltas = np.array([o["deltas"] for o in out]); r = np.quantile(deltas, 0.9, axis=0)
        on = np.all(deltas <= r[None, :], axis=1)
        bK, bL, bl, oneR, gG, eE = bounds_for_radius(I, Rt, 0.0)
        Lon = np.zeros(len(out)); Loff = np.zeros(len(out))
        Lh, _ = lam_norms(I)
        for i, o in enumerate(out):
            M = o["Mstar"]; X = np.linalg.norm(Lh @ x0)
            for t in range(I["T"]):
                bK_t, bL_t, bl_t, oneR_t, _, _ = bounds_for_radius(I, Rt, r[t]); bK_t, bL_t, bl_t = bK_t[t], bL_t[t], bl_t[t]
                Lon[i] += I["rho"] ** t * 0.5 * oneR[t] * (bK_t * X + bL_t * M + bl_t) ** 2
                Loff[i] += I["rho"] ** t * 0.5 * oneR[t] * (2 * X + 2 * gG * (I["T"] - t) * M + 2 * eE * (I["T"] - t)) ** 2
                X = X + gG * (I["T"] - t) * M + eE * (I["T"] - t)
        # pathwise: on the event the realized loss is at most Lon; off it at most Loff
        assert np.all(idents[on] <= Lon[on] + 1e-9) and np.all(idents <= Loff + 1e-9)
        alpha = 1 - on.mean()
        guarantee = Lon.mean() + np.sqrt(alpha) * np.sqrt((Loff ** 2).mean())
        assert idents.mean() <= guarantee
        print(f"  pre-sample {n0}: identity in expectation (MC gap {gaps.mean():.3e}, identity {idents.mean():.3e}, SE {se:.1e}); a priori coefficient and position bounds hold on all 300 paths; "
              f"P(off event) {alpha:.2f}; MC loss {idents.mean():.3e} <= on-event term {Lon.mean():.3e} + sqrt(alpha) off-event term {np.sqrt(alpha) * np.sqrt((Loff ** 2).mean()):.3e}")
    print("checks/035: all checks passed")


if __name__ == "__main__":
    main()
    sys.exit(0)
