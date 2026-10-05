"""Red's reproduction of experiment 025 (persistent alpha and premia, implementable space), written from the
registered Design and model/SPEC.md M5, without reading run.py or report.py. Instance and truth draws from
red's experiment 022 reproduction; constraints and convex programs as in red's experiment 024 reproduction.
Red's own seeds; common random numbers across cells (theta_0 and return shocks from (9025, r), state
innovations from (9125, r), scaled by each cell's Q^(1/2)).

Usage: uv run python experiments/025/red_reproduce.py <ff5 zip> <R> <procs> <cell> [<cell> ...]
"""
import importlib.util, os, sys
import numpy as np
import cvxpy as cp
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("r22", os.path.join(HERE, "..", "022", "red_reproduce.py"))
r22 = importlib.util.module_from_spec(spec); spec.loader.exec_module(r22)
T, GAMMA, FCAP, ECAP = 40, 5.0, 0.10, 1.0
CELLS = {"A50": (0.50, 1.0), "A80": (0.80, 1.0), "A95": (0.95, 1.0), "L50": (1.0, 0.50), "L80": (1.0, 0.80),
         "L95": (1.0, 0.95), "B80": (0.80, 0.80)}
S = None; CFG = {}


def chol(A):
    return np.linalg.cholesky(A + 1e-14 * np.eye(len(A))).T


def init(path, cell):
    global S
    S = r22.setup(r22.factors(path))
    rA, rL = CELLS[cell]
    K, N = S["K"], S["N"]
    phi = np.r_[np.full(K, rL), np.full(N, rA)]
    Q = np.zeros((K + N, K + N))
    Q[:K, :K] = (1 - rL ** 2) * S["P0"][:K, :K]; Q[K:, K:] = (1 - rA ** 2) * S["P0"][K:, K:]
    Rn = np.zeros((K + N, K + N)); Rn[:K, :K] = S["Sf"]; Rn[K:, K:] = np.diag(S["sA"] ** 2)
    P = [S["P0"]]; Pplus = []
    for t in range(T):
        Pp = np.linalg.inv(np.linalg.inv(P[-1]) + np.linalg.inv(Rn)); Pplus.append(Pp)
        P.append(np.diag(phi) @ Pp @ np.diag(phi) + Q)
    Sig = [S["G"] @ P[t] @ S["G"].T + S["Sr"] for t in range(T + 8)] if False else [S["G"] @ P[t] @ S["G"].T + S["Sr"] for t in range(T)]
    CFG.update(phi=phi, Q=Q, Qh=np.linalg.cholesky(Q + 1e-30 * np.eye(K + N)) if Q.any() else np.zeros_like(Q),
               Rn=Rn, P=P, Pplus=Pplus, Sig=Sig, C=[chol(s) for s in Sig], Cr=chol(S["Sr"]), tb=S["m0"].copy())


class MPC:
    def __init__(self, H, fix_funds=False, fibre=False):
        n, N, K = S["n"], S["N"], S["K"]; lam = np.diag(S["Lam"])
        self.xp = cp.Parameter(n); self.mu = [cp.Parameter(n) for _ in range(H)]
        self.C = [cp.Parameter((n, n)) for _ in range(H)]; self.X = cp.Variable((n, H))
        cap = np.r_[np.full(N, FCAP), np.full(S["M"], ECAP)]
        obj, cons, prev = 0, [], self.xp
        for k in range(H):
            x = self.X[:, k]; u = x - prev; q = cp.sum(cp.multiply(lam, cp.square(u)))
            obj += x @ self.mu[k] - GAMMA / 2 * cp.sum_squares(self.C[k] @ x) - 0.5 * q
            cons += [x >= 0, x <= cap, cp.sum(x) + 0.5 * q <= 1]
            if fix_funds: cons += [x[:N] == self.xp[:N]]
            prev = x
        if fibre:
            self.b = cp.Parameter(K); cons += [S["B"].T @ self.X[:, 0] == self.b]
        self.prob = cp.Problem(cp.Maximize(obj), cons)

    def solve(self, xp, mus, Cs, b=None):
        self.xp.value = xp
        for p, v in zip(self.mu, mus): p.value = v
        for p, v in zip(self.C, Cs): p.value = v
        if b is not None: self.b.value = b
        self.prob.solve(solver=cp.CLARABEL)
        return np.maximum(self.X.value[:, 0], 0.0)


class Stage1:
    def __init__(self):
        n, N, K = S["n"], S["N"], S["K"]; lam = np.diag(S["Lam"])
        self.xp = cp.Parameter(n); self.lh = cp.Parameter(K); self.C = cp.Parameter((K, K))
        x = cp.Variable(n); u = x - self.xp; q = cp.sum(cp.multiply(lam, cp.square(u))); b = S["B"].T @ x
        cap = np.r_[np.full(N, FCAP), np.full(S["M"], ECAP)]; self.x = x
        self.prob = cp.Problem(cp.Maximize(b @ self.lh - GAMMA / 2 * cp.sum_squares(self.C @ b) - 1e-9 * cp.sum_squares(u)),
                               [x >= 0, x <= cap, cp.sum(x) + 0.5 * q <= 1])

    def solve(self, xp, lh, Cf):
        self.xp.value = xp; self.lh.value = lh; self.C.value = Cf
        self.prob.solve(solver=cp.CLARABEL); return S["B"].T @ self.x.value


def path(r):
    N, K, n, G, B = S["N"], S["K"], S["n"], S["G"], S["B"]
    Lam, Sr, x0, cE = S["Lam"], S["Sr"], S["x0"], S["cE"]
    phi, Qh, Rn, P, Pplus, C, Cr, tb = (CFG[k] for k in ("phi", "Qh", "Rn", "P", "Pplus", "C", "Cr", "tb"))
    g0 = np.r_[np.zeros(N), -cE]
    rng = np.random.default_rng((9025, r)); rng2 = np.random.default_rng((9125, r))
    lam0 = rng.multivariate_normal(S["lam_hat"], S["Sf"] / 248)
    alpha0 = rng.choice([-0.008, 0.0, 0.0095], size=N, p=[0.240, 0.754, 0.006])
    zf = rng.multivariate_normal(np.zeros(K), S["Sf"], size=T); zA = rng.normal(0, S["sA"], (T, N))
    eta = rng2.normal(size=(T, K + N))
    th = np.r_[lam0, alpha0]
    m = S["m0"].copy()
    mpc = {H: MPC(H) for H in range(1, 9)}; etf = {H: MPC(H, fix_funds=True) for H in range(1, 9)}
    fib = MPC(1, fibre=True); st1 = Stage1()
    names = ["MPC-L", "MPC-S", "MPC-flat", "MPC-L4", "rule", "ETF-only", "two-stage"]
    x = {k: x0.copy() for k in names}; tot = {k: 0.0 for k in names}
    zero = {k: 0.0 for k in names}; turn = {k: np.zeros(2) for k in names}
    for t in range(T):
        mu_t = G @ m + g0
        H = min(8, T - t); H4 = min(4, T - t)
        fc = [G @ (phi ** k * m + (1 - phi ** k) * tb) + g0 for k in range(H)]
        new = {}
        new["MPC-L"] = mpc[H].solve(x["MPC-L"], fc, C[t:t + H])
        new["MPC-S"] = mpc[H].solve(x["MPC-S"], fc, [C[t]] * H)
        new["MPC-flat"] = mpc[H].solve(x["MPC-flat"], [mu_t] * H, C[t:t + H])
        new["MPC-L4"] = mpc[H4].solve(x["MPC-L4"], fc[:H4], C[t:t + H4])
        new["rule"] = mpc[1].solve(x["rule"], [mu_t], [Cr])
        new["ETF-only"] = etf[H].solve(x["ETF-only"], fc, C[t:t + H])
        b = st1.solve(x["two-stage"], m[:K], chol(S["Sf"] + P[t][:K, :K]))
        new["two-stage"] = fib.solve(x["two-stage"], [mu_t], [C[t]], b=b)
        mu_true = G @ th + g0
        for k in names:
            xx = new[k]; u = xx - x[k]
            tot[k] += xx @ mu_true - GAMMA / 2 * xx @ Sr @ xx - 0.5 * u @ Lam @ u
            zero[k] += np.mean(xx[:N] <= 1e-6) / T
            turn[k] += np.array([np.abs(u[:N]).sum(), np.abs(u[N:]).sum()]) / T
            x[k] = xx
        # observe returns at the current truth, update, then predict; the truth moves
        y = np.r_[th[:K] + zf[t], th[K:] + zA[t]]
        mp = Pplus[t] @ (np.linalg.solve(P[t], m) + np.linalg.solve(Rn, y))
        m = phi * mp + (1 - phi) * tb
        th = phi * th + (1 - phi) * tb + Qh @ eta[t]
    return {k: (tot[k] / T * 1e4, zero[k], turn[k]) for k in names}


def run_cell(zp, cell, R, procs):
    with Pool(procs, initializer=init, initargs=(zp, cell)) as pool:
        return pool.map(path, range(R))


if __name__ == "__main__":
    zp, R, procs = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    se = lambda v: v.std(ddof=1) / np.sqrt(len(v))
    for cell in sys.argv[4:]:
        res = run_cell(zp, cell, R, procs)
        ce = {k: np.array([q[k][0] for q in res]) for k in res[0]}
        d = lambda a, b: (ce[a] - ce[b]).mean(), lambda a, b: se(ce[a] - ce[b])
        f = lambda a, b: f"{(ce[a]-ce[b]).mean():.3f} ({se(ce[a]-ce[b]):.3f})"
        z = {k: np.mean([q[k][1] for q in res]) for k in ("MPC-L", "rule")}
        tu = {k: np.mean([q[k][2] for q in res], axis=0) for k in ("MPC-L", "rule")}
        print(f"{cell} R={R}: MPC-L CE {ce['MPC-L'].mean():.2f}; dyn+learn {f('MPC-L','rule')}; learning {f('MPC-L','MPC-S')}; "
              f"aim-in-front {f('MPC-L','MPC-flat')}; H8-H4 {f('MPC-L','MPC-L4')}; minus two-stage {f('MPC-L','two-stage')}; "
              f"minus ETF-only {f('MPC-L','ETF-only')}; funds at zero {z['MPC-L']:.3f}/{z['rule']:.3f}; "
              f"fund turnover {tu['MPC-L'][0]:.4f}/{tu['rule'][0]:.4f}; ETF turnover {tu['MPC-L'][1]:.4f}/{tu['rule'][1]:.4f}", flush=True)
