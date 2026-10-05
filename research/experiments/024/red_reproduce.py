"""Red's reproduction of experiment 024, written from the registered Design (and model/SPEC.md M5), without
reading run.py, compact.py or report.py. The instance, true-parameter draws and filter are red's own
experiment 022 reproduction (experiments/022/red_reproduce.py): red's own draw of the 30 funds and red's own
path seeds, so agreement is in magnitude and ordering, not exact values.

Usage: uv run python experiments/024/red_reproduce.py <ff5 zip> <R> [procs]
"""
import importlib.util, os, sys
import numpy as np
import cvxpy as cp
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("r22", os.path.join(HERE, "..", "022", "red_reproduce.py"))
r22 = importlib.util.module_from_spec(spec); spec.loader.exec_module(r22)
T, GAMMA = 40, 5.0
FCAP, ECAP = 0.10, 1.0
S = P = Rn = Sig = None


def init(path):
    global S, P, Rn, Sig
    S = r22.setup(r22.factors(path))
    P, Rn = r22.filter_path(S, T)
    Sig = [S["G"] @ P[t] @ S["G"].T + S["Sr"] for t in range(T)]


def chol(A):
    return np.linalg.cholesky(A + 1e-14 * np.eye(len(A))).T      # A = L'L -> ||L x||^2 = x'Ax


class MPC:
    """max sum_k x_k'mu - g/2 ||C_k x_k||^2 - 1/2 u_k'Lam u_k s.t. x_k >= 0, caps, 1'x_k + 1/2 u_k'Lam u_k <= 1."""
    def __init__(self, H, fix_funds=False, fibre=False):
        n, N, K = S["n"], S["N"], S["K"]
        lam = np.diag(S["Lam"])
        self.xp = cp.Parameter(n); self.mu = cp.Parameter(n)
        self.C = [cp.Parameter((n, n)) for _ in range(H)]
        self.X = cp.Variable((n, H))
        cap = np.r_[np.full(N, FCAP), np.full(S["M"], ECAP)]
        obj, cons, prev = 0, [], self.xp
        for k in range(H):
            x = self.X[:, k]; u = x - prev
            q = cp.sum(cp.multiply(lam, cp.square(u)))
            obj += x @ self.mu - GAMMA / 2 * cp.sum_squares(self.C[k] @ x) - 0.5 * q
            cons += [x >= 0, x <= cap, cp.sum(x) + 0.5 * q <= 1]
            if fix_funds:
                cons += [x[:N] == self.xp[:N]]
            prev = x
        if fibre:
            self.b = cp.Parameter(K); cons += [S["B"].T @ self.X[:, 0] == self.b]
        self.prob = cp.Problem(cp.Maximize(obj), cons)

    def solve(self, xp, mu, Cs, b=None):
        self.xp.value = xp; self.mu.value = mu
        for Cp, Cv in zip(self.C, Cs):
            Cp.value = Cv
        if b is not None:
            self.b.value = b
        self.prob.solve(solver=cp.CLARABEL)
        return np.maximum(self.X.value[:, 0], 0.0)


class Stage1:
    """two-stage stage 1: argmax over x in F_t of b'lam_hat - g/2 b'(Sf + P_lam) b, b = B'x."""
    def __init__(self):
        n, N, K = S["n"], S["N"], S["K"]
        lam = np.diag(S["Lam"])
        self.xp = cp.Parameter(n); self.lh = cp.Parameter(K); self.C = cp.Parameter((K, K))
        x = cp.Variable(n); u = x - self.xp; q = cp.sum(cp.multiply(lam, cp.square(u)))
        b = S["B"].T @ x
        cap = np.r_[np.full(N, FCAP), np.full(S["M"], ECAP)]
        self.x = x
        self.prob = cp.Problem(cp.Maximize(b @ self.lh - GAMMA / 2 * cp.sum_squares(self.C @ b) - 1e-9 * cp.sum_squares(u)),
                               [x >= 0, x <= cap, cp.sum(x) + 0.5 * q <= 1])

    def solve(self, xp, lh, Cf):
        self.xp.value = xp; self.lh.value = lh; self.C.value = Cf
        self.prob.solve(solver=cp.CLARABEL)
        return S["B"].T @ self.x.value


def equal_weight():
    n = S["n"]; lam = np.diag(S["Lam"]); x0 = S["x0"]
    lo, hi = 0.0, 1.0 / n
    for _ in range(100):
        w = (lo + hi) / 2; u = w - x0
        if n * w + 0.5 * np.sum(lam * u * u) <= 1: lo = w
        else: hi = w
    return np.full(n, lo)


def path(args):
    r, H8 = args
    N, K, n, G, B = S["N"], S["K"], S["n"], S["G"], S["B"]
    Lam, Sr, x0, cE = S["Lam"], S["Sr"], S["x0"], S["cE"]
    rng = np.random.default_rng((9024, r))
    lamv = rng.multivariate_normal(S["lam_hat"], S["Sf"] / 248)
    alpha = rng.choice([-0.008, 0.0, 0.0095], size=N, p=[0.240, 0.754, 0.006])
    mu_true = np.r_[B[:N] @ lamv + alpha, B[N:] @ lamv - cE]
    zf = rng.multivariate_normal(np.zeros(K), S["Sf"], size=T); zA = rng.normal(0, S["sA"], (T, N))
    Cs = [chol(Sig[t]) for t in range(T)]; Cr = chol(Sr)
    mpc = {H: MPC(H) for H in range(1, 5)}; etf = {H: MPC(H, fix_funds=True) for H in range(1, 5)}
    fib = MPC(1, fibre=True); st1 = Stage1()
    if H8:
        mpc8 = {H: MPC(H) for H in range(1, 9)}
    names = ["MPC-L", "MPC-S", "myopic", "ETF-only", "two-stage", "equal", "no trade"] + (["MPC-L H8"] if H8 else [])
    x = {k: x0.copy() for k in names}; tot = {k: 0.0 for k in names}
    zero = {k: np.zeros(n) for k in names}; inv = {k: 0.0 for k in names}; bind = {k: 0 for k in names}
    ew = equal_weight(); m = S["m0"].copy()
    for t in range(T):
        mu_t = G @ m + np.r_[np.zeros(N), -cE]
        H = min(4, T - t)
        new = {}
        new["MPC-L"] = mpc[H].solve(x["MPC-L"], mu_t, Cs[t:t + H])
        new["MPC-S"] = mpc[H].solve(x["MPC-S"], mu_t, [Cs[t]] * H)
        new["myopic"] = mpc[1].solve(x["myopic"], mu_t, [Cr])
        new["ETF-only"] = etf[H].solve(x["ETF-only"], mu_t, Cs[t:t + H])
        b = st1.solve(x["two-stage"], m[:K], chol(S["Sf"] + P[t][:K, :K]))
        new["two-stage"] = fib.solve(x["two-stage"], mu_t, [Cs[t]], b=b)
        new["equal"] = ew if t == 0 else x["equal"]
        new["no trade"] = x["no trade"]
        if H8:
            H_ = min(8, T - t); new["MPC-L H8"] = mpc8[H_].solve(x["MPC-L H8"], mu_t, Cs[t:t + H_])
        lam = np.diag(Lam)
        for k in names:
            xx = new[k]; u = xx - x[k]
            tot[k] += xx @ mu_true - GAMMA / 2 * xx @ Sr @ xx - 0.5 * u @ Lam @ u
            zero[k] += (xx <= 1e-6) / T; inv[k] += xx.sum() / T
            bind[k] += (xx.sum() + 0.5 * np.sum(lam * u * u) >= 1 - 1e-6) / T
            x[k] = xx
        y = np.r_[lamv + zf[t], alpha + zA[t]]
        m = P[t + 1] @ (np.linalg.solve(P[t], m) + np.linalg.solve(Rn, y))
    return {k: (tot[k] / T * 1e4, zero[k], inv[k], bind[k]) for k in names}


if __name__ == "__main__":
    zp, R = sys.argv[1], int(sys.argv[2]); procs = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    H8 = len(sys.argv) > 4 and sys.argv[4] == "h8"
    with Pool(procs, initializer=init, initargs=(zp,)) as pool:
        res = pool.map(path, [(r, H8) for r in range(R)])
    init(zp); N = S["N"]
    se = lambda v: v.std(ddof=1) / np.sqrt(len(v))
    names = list(res[0].keys())
    ce = {k: np.array([q[k][0] for q in res]) for k in names}
    print(f"R = {R} (red's paths and universe); CE bp/q mean (SE); MPC-L minus policy (SE); funds at zero mean (min-max over funds); ETFs at zero; invested; budget binding")
    for k in names:
        d = ce["MPC-L"] - ce[k]
        zf = np.mean([q[k][1][:N] for q in res], axis=0); ze = np.mean([q[k][1][N:] for q in res])
        print(f"  {k:10s} {ce[k].mean():8.2f} ({se(ce[k]):.2f})  {d.mean():8.3f} ({se(d):.3f})  {zf.mean():.3f} ({zf.min():.3f}-{zf.max():.3f})  {ze:.3f}  "
              f"{np.mean([q[k][2] for q in res]):.3f}  {np.mean([q[k][3] for q in res]):.3f}")
