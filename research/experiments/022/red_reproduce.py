"""Red's reproduction of experiment 022 (Parts 1-2), written from the registered Design and model/SPEC.md M5,
without reading run.py, model.py, stationary.py or report.py.

The fund universe is drawn from the Design's distributions with red's own generator (the Design does not
fix the draw order, so red's 30 funds differ from the analyst's); paths use red's own seeds. Agreement is
therefore in magnitude and ordering, not in exact values. The FF5 file is read from the registered cache
(SHA-256 checked) and never committed.

Usage: uv run python experiments/022/red_reproduce.py [path to ff5 zip] [R]
"""
import hashlib, io, sys, zipfile
import numpy as np

SHA = "42492fc7fe23de2c44058e77414e1d35c451bf8d289dfff75c5b80c2804324e2"


def factors(path):
    raw = open(path, "rb").read(); assert hashlib.sha256(raw).hexdigest() == SHA
    z = zipfile.ZipFile(io.BytesIO(raw)); txt = z.read(z.namelist()[0]).decode("latin-1")
    rows = []
    for line in txt.splitlines():
        p = [x.strip() for x in line.split(",")]
        if len(p) >= 7 and len(p[0]) == 6 and p[0].isdigit():
            rows.append((int(p[0]), [float(x) / 100 for x in p[1:7]]))
    rows = [r for r in rows if 196307 <= r[0] <= 202506]
    M = np.array([r[1] for r in rows]); assert len(M) == 744
    rf = M[:, 5].reshape(248, 3); F5 = M[:, :5].reshape(248, 3, 5)
    Q = np.prod(1 + F5, axis=1) - 1                       # long-short factors: compounded directly
    # market excess: compounded market return (Mkt-RF + RF) less compounded risk-free return
    Q[:, 0] = np.prod(1 + F5[:, :, 0] + rf, axis=1) - np.prod(1 + rf, axis=1)
    return Q


def setup(Q, seed=2022):
    K, N, M = 5, 30, 8
    lam_hat = Q.mean(0); Sf = np.cov(Q.T)
    rng = np.random.default_rng(seed)
    BA = np.column_stack([rng.uniform(0.85, 1.15, N), rng.normal(0, 0.3, (N, 4))])
    sA = rng.uniform(0.01, 0.03, N)
    BE = np.array([[1, 0, 0, 0, 0], [1, .8, .2, 0, 0], [1, 0, .6, 0, 0], [1, 0, -.4, 0, 0],
                   [1, 0, 0, .4, 0], [1, 0, 0, 0, .4], [1, .8, .6, 0, 0], [1, .3, .1, 0, 0]], float)
    cE = np.array([1, 4, 4, 4, 5, 5, 5, 5]) * 1e-4
    sE = np.full(M, 0.003)
    B = np.vstack([BA, BE]); n = N + M
    G = np.zeros((n, K + N)); G[:, :K] = B; G[:N, K:] = np.eye(N)
    Sr = B @ Sf @ B.T + np.diag(np.r_[sA ** 2, sE ** 2])
    mu_a, sbar, stot = -0.0019, 0.000625, 0.0035
    s2 = stot ** 2 - sbar ** 2
    P0 = np.zeros((K + N, K + N)); P0[:K, :K] = Sf / 248; P0[K:, K:] = sbar ** 2 * np.ones((N, N)) + s2 * np.eye(N)
    m0 = np.r_[lam_hat, np.full(N, mu_a)]
    Lam = np.diag(np.r_[np.full(N, 0.1), np.full(M, 0.01)])
    x0 = np.r_[np.full(N, 0.5 / N), 0.5, np.zeros(M - 1)]
    return dict(K=K, N=N, M=M, n=n, B=B, G=G, Sf=Sf, Sr=Sr, sA=sA, cE=cE, P0=P0, m0=m0, Lam=Lam, x0=x0, lam_hat=lam_hat)


def filter_path(S, T):
    """Deterministic P_t (baseline Phi = I, Q = 0): premia from f (noise Sf), alphas from residuals (noise diag sA^2)."""
    K, N = S["K"], S["N"]
    R = np.zeros((K + N, K + N)); R[:K, :K] = S["Sf"]; R[K:, K:] = np.diag(S["sA"] ** 2)
    P = [S["P0"]]
    for t in range(T):
        P.append(np.linalg.inv(np.linalg.inv(P[-1]) + np.linalg.inv(R)))
    return P, R


def recursion(S, Sig, T, gamma, sel=None, known_mu=None):
    """Backward LQ recursion. State (x_-, m, 1); stage: x = x_- + Sel v; value -> policy x = Kx x_- + Km m + k.
    Sig: list of covariances used in the stage objective. known_mu: fixed true mean (oracle)."""
    n, G, Lam = S["n"], S["G"], S["Lam"]
    dm = G.shape[1]
    Sel = np.eye(n) if sel is None else sel
    mu0 = np.r_[np.zeros(S["N"]), -S["cE"]]
    if known_mu is not None:
        Mm = np.zeros((n, dm)); mu0 = known_mu
    else:
        Mm = G
    dz = n + dm + 1
    H = np.zeros((dz, dz)); pols = [None] * T
    for t in reversed(range(T)):
        # choose v (dim k): x = y + Sel v, y = x_-; objective in w = (v, y, m, 1)
        k = Sel.shape[1]
        E = np.zeros((n, k + dz)); E[:, :k] = Sel; E[:, k:k + n] = np.eye(n)       # x = E w
        Mw = np.zeros((n, k + dz)); Mw[:, k + n:k + n + dm] = Mm; Mw[:, -1] = mu0   # mu = Mw w
        U = np.zeros((n, k + dz)); U[:, :k] = Sel                                   # u = U w
        Z = np.zeros((dz, k + dz)); Z[:n, :] = E; Z[n:, k + n:] = np.eye(dm + 1)    # z' = (x, m, 1) (m' mean m)
        W = E.T @ Mw + Mw.T @ E - gamma * E.T @ Sig[t] @ E - U.T @ Lam @ U + Z.T @ H @ Z
        Wvv, Wvr = W[:k, :k], W[:k, k:]
        Kf = -np.linalg.solve(Wvv, Wvr)
        pols[t] = Kf
        H = W[k:, k:] - Wvr.T @ np.linalg.solve(Wvv, Wvr)
    return pols


def simulate(S, T, gamma, R_paths, seed0=922, only=None):
    P, Rn = filter_path(S, T)
    K, N, M, n, G, B = S["K"], S["N"], S["M"], S["n"], S["G"], S["B"]
    Sig = [G @ P[t] @ G.T + S["Sr"] for t in range(T)]
    pol = {"D12": recursion(S, Sig, T, gamma), "static": recursion(S, [Sig[0]] * T, T, gamma)}
    selE = np.zeros((n, M)); selE[N:, :] = np.eye(M)
    pol["ETF-only"] = recursion(S, Sig, T, gamma, sel=selE)
    names = ["D12", "myopic", "static", "ETF-only", "two-stage", "equal", "no trade", "oracle"]
    ce = {k: np.zeros(R_paths) for k in names}
    extra = {k: dict(alpha=np.zeros(R_paths), alpha_short=np.zeros(R_paths), short=np.zeros(R_paths), lev=np.zeros(R_paths)) for k in names}
    Lam, Sr, x0 = S["Lam"], S["Sr"], S["x0"]
    cE = S["cE"]
    Wmy = gamma * Sr + Lam
    for r in range(R_paths):
        rng = np.random.default_rng((9022, r))
        lam = rng.multivariate_normal(S["lam_hat"], S["Sf"] / 248)
        alpha = rng.choice([-0.008, 0.0, 0.0095], size=N, p=[0.240, 0.754, 0.006])
        mu_true = np.r_[B[:N] @ lam + alpha, B[N:] @ lam - cE]
        zf = rng.multivariate_normal(np.zeros(K), S["Sf"], size=T); zA = rng.normal(0, S["sA"], (T, N))
        # oracle policy for this path
        pol_or = recursion(S, [Sr] * T, T, gamma, known_mu=mu_true)
        m = S["m0"].copy()
        x = {k: x0.copy() for k in names}
        tot = {k: 0.0 for k in names}
        for t in range(T):
            mu_t = G @ m + np.r_[np.zeros(N), -cE]
            new = {}
            for k in ("D12", "static", "ETF-only"):
                zz = np.r_[x[k], m, 1.0]; kf = pol[k][t] @ zz
                new[k] = x[k] + (kf if k != "ETF-only" else np.r_[np.zeros(N), kf])
            zz = np.r_[x["oracle"], m, 1.0]; new["oracle"] = x["oracle"] + pol_or[t] @ zz
            new["myopic"] = np.linalg.solve(Wmy, mu_t + Lam @ x["myopic"])
            # two-stage: b* = (gamma (Sf + P_lambda))^-1 m_lambda; max x'mu - g/2 x'Sig x - 1/2 (x-x_)'Lam(x-x_) s.t. B'x = b*
            bstar = np.linalg.solve(gamma * (S["Sf"] + P[t][:K, :K]), m[:K])
            Wq = gamma * Sig[t] + Lam
            KKT = np.block([[Wq, B], [B.T, np.zeros((K, K))]])
            sol = np.linalg.solve(KKT, np.r_[mu_t + Lam @ x["two-stage"], bstar]); new["two-stage"] = sol[:n]
            new["equal"] = np.full(n, 1.0 / n); new["no trade"] = x["no trade"]
            for k in names:
                u = new[k] - x[k]; xx = new[k]
                tot[k] += xx @ mu_true - gamma / 2 * xx @ Sr @ xx - 0.5 * u @ Lam @ u
                a = xx[:N]
                extra[k]["alpha"][r] += a @ alpha / T; extra[k]["alpha_short"][r] += np.minimum(a, 0) @ alpha / T
                extra[k]["short"][r] += np.mean(a < 0) / T; extra[k]["lev"][r] += np.abs(xx).sum() / T
                x[k] = xx
            # observe and update (decoupled filter; Phi = I)
            f = lam + zf[t]; res = alpha + zA[t]
            y = np.r_[f, res]
            Pt, Pn = P[t], P[t + 1]
            m = Pn @ (np.linalg.solve(Pt, m) + np.linalg.solve(Rn, y))
        for k in names:
            ce[k][r] = tot[k] / T * 1e4
    return ce, extra, pol, Sig, P


if __name__ == "__main__" and len(sys.argv) > 3 and sys.argv[3] == "sens":
    Q = factors(sys.argv[1]); Rp = int(sys.argv[2]); se = lambda v: v.std(ddof=1) / np.sqrt(len(v))
    S = setup(Q); n, N = S["n"], S["N"]
    P, _ = filter_path(S, 40); Sig = [S["G"] @ P[t] @ S["G"].T + S["Sr"] for t in range(40)]
    Kf = recursion(S, Sig, 40, 5.0)[0]; Gam = -Kf[:, :n]; aim = np.linalg.solve(Gam, Kf[:, n:] @ np.r_[S["m0"], 1.0])
    print(f"aim at t=0 (prior means): gross funds {np.abs(aim[:N]).sum():.2f}, ETFs {np.abs(aim[N:]).sum():.2f}; net funds {aim[:N].sum():.2f}, ETFs {aim[N:].sum():.2f}")
    for lab, g, la in (("gamma 2", 2.0, 0.1), ("gamma 10", 10.0, 0.1), ("lambda_A 0.5", 5.0, 0.5)):
        S2 = setup(Q); S2["Lam"] = np.diag(np.r_[np.full(N, la), np.full(S2["M"], 0.01)])
        ce, _, _, _, _ = simulate(S2, 40, g, Rp)
        a, b, c = ce["D12"] - ce["ETF-only"], ce["D12"] - ce["two-stage"], ce["oracle"] - ce["D12"]
        print(f"{lab}: D12-ETF-only {a.mean():.1f} ({se(a):.2f}); D12-two-stage {b.mean():.1f} ({se(b):.2f}); oracle-D12 {c.mean():.1f} ({se(c):.2f})")
    sys.exit(0)


if __name__ == "__main__":
    path = sys.argv[1] if len(sys.argv) > 1 else "../analyst/experiments/022/cache/ff5_2025-07cut.zip"
    Rp = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    Q = factors(path)
    print("FF5 quarterly means (%):", np.round(Q.mean(0) * 100, 3), "SDs (%):", np.round(Q.std(0, ddof=1) * 100, 3))
    S = setup(Q)
    ce, extra, pol, Sig, P = simulate(S, 40, 5.0, Rp)
    se = lambda v: v.std(ddof=1) / np.sqrt(len(v))
    print(f"\nPart 1 (R = {Rp}, red's own universe and paths): CE bp/q mean (SE); D12 minus policy (SE)")
    for k in ce:
        d = ce["D12"] - ce[k]
        print(f"  {k:10s} {ce[k].mean():8.1f} ({se(ce[k]):.1f})   {d.mean():8.2f} ({se(d):.2f})")
    print("\nPart 2: alpha captured bp/q, of which from shorts; share of fund-quarters short; gross leverage")
    for k in ("D12", "myopic", "static", "ETF-only", "two-stage", "oracle"):
        e = extra[k]
        print(f"  {k:10s} {e['alpha'].mean() * 1e4:8.1f}  {e['alpha_short'].mean() * 1e4:8.1f}  {e['short'].mean():.3f}  {e['lev'].mean():.2f}")
    n, N = S["n"], S["N"]
    for t in (0, 20, 39):
        Kx = pol["D12"][t][:, :n]
        sp = np.diag(-Kx)          # x = x_- + Kx x_- + ...: fraction closed = -diag(Kx) when K acts on the trade
        print(f"  speed t={t}: funds {sp[:N].mean():.3f}, ETFs {sp[N:].mean():.3f}")
