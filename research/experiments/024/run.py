"""Experiment 024: experiment 022 in the implementable space (M5 beliefs and quadratic costs; long-only, funded, capped).
Registered design: experiments/024-m5-constrained-value.md.

Reuses experiment 022's calibrated instance and filter (experiments/022/model.py) and its path seeds (2022, r).
Every policy solves its per-quarter convex program exactly (CLARABEL) under the constraints
    x >= 0,   1'x + C(u) <= 1,   x_fund <= 0.10,   x_ETF <= 1,
with C(u) = (1/2) u' Lambda u (M5) or kappa'|u| (the proportional-cost band variant).
Run:    uv run python experiments/024/run.py [part]       parts: main, h8, sens, prop  (writes experiments/024/<part>.json)
Report: uv run python experiments/024/report.py
"""
import importlib.util
import json
import os
import sys
import time
from multiprocessing import Pool
from pathlib import Path

import cvxpy as cp
import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
_s = importlib.util.spec_from_file_location("m022", ROOT / "experiments" / "022" / "model.py")
m022 = importlib.util.module_from_spec(_s); _s.loader.exec_module(m022)
m022.CACHE = HERE / "cache"

CAP_FUND, CAP_ETF = 0.10, 1.0
KAPPA = (0.01, 0.0005)          # proportional variant: fund 100 bp, ETF 5 bp
POLICIES = ["MPC-L", "MPC-S", "myopic", "ETF-only", "two-stage", "equal", "no-trade"]
_I = {}


def inst(delta):
    if delta not in _I:
        I = m022.Inst()
        I.m0 = I.m0.copy(); I.m0[:I.N] += delta
        I.delta = delta
        I.caps = np.concatenate([np.full(I.N, CAP_FUND), np.full(I.M, CAP_ETF)])
        I.Lchol = [np.linalg.cholesky(I.S(t)) for t in range(I.T + 1)]
        I.Lr = np.linalg.cholesky(I.Sigma_r)
        _I[delta] = I
    return _I[delta]


class Program:
    """max sum_k x_k'mu - (gamma/2)|L_k' x_k|^2 - C(u_k), s.t. constraints at every k; parameters x_prev, mu, L_k."""

    def __init__(self, I, H, cost="quad", frozen=None, fibre=False, zero_cost=False):
        n = I.n
        self.H = H
        self.xp = cp.Parameter(n); self.mu = cp.Parameter(n)
        self.L = [cp.Parameter((n, n)) for _ in range(H)]
        self.x = [cp.Variable(n) for _ in range(H)]
        self.b = cp.Parameter(I.K) if fibre else None
        obj, cons = 0, []
        prev = self.xp
        for k in range(H):
            u = self.x[k] - prev
            if zero_cost:
                C = 0
            elif cost == "quad":
                C = 0.5 * cp.sum(cp.multiply(I.Lam, cp.square(u)))
            else:
                C = cp.sum(cp.multiply(np.concatenate([np.full(I.N, KAPPA[0]), np.full(I.M, KAPPA[1])]), cp.abs(u)))
            obj += self.mu @ self.x[k] - 0.5 * I.gamma * cp.sum_squares(self.L[k].T @ self.x[k]) - C
            cons += [self.x[k] >= 0, self.x[k] <= I.caps, cp.sum(self.x[k]) + C <= 1]
            if frozen is not None:
                cons += [self.x[k][frozen] == self.xp[frozen]]
            prev = self.x[k]
        if fibre:
            cons += [I.B.T @ self.x[0] == self.b]
        self.prob = cp.Problem(cp.Maximize(obj), cons)

    def solve(self, xp, mu, Ls, b=None):
        self.xp.value = xp; self.mu.value = mu
        for k in range(self.H):
            self.L[k].value = Ls[k]
        if b is not None:
            self.b.value = b
        self.prob.solve(solver="CLARABEL")
        if self.prob.status not in ("optimal", "optimal_inaccurate"):
            raise RuntimeError(self.prob.status)
        return np.clip(self.x[0].value, 0.0, None)


class Stage1:
    """Two-stage stage 1: b* = argmax_b G(b) over b(F_t), as a program in x: max (B'x)'mu_f - (gamma/2)|L_f' B'x|^2."""

    def __init__(self, I):
        n = I.n
        self.xp = cp.Parameter(n); self.muf = cp.Parameter(I.K); self.Lf = cp.Parameter((I.K, I.K))
        self.x = cp.Variable(n)
        u = self.x - self.xp
        C = 0.5 * cp.sum(cp.multiply(I.Lam, cp.square(u)))
        b = I.B.T @ self.x
        self.prob = cp.Problem(cp.Maximize(self.muf @ b - 0.5 * I.gamma * cp.sum_squares(self.Lf.T @ b)),
                               [self.x >= 0, self.x <= I.caps, cp.sum(self.x) + C <= 1])
        self.B = I.B

    def solve(self, xp, muf, Lf):
        self.xp.value = xp; self.muf.value = muf; self.Lf.value = Lf
        self.prob.solve(solver="CLARABEL")
        return self.B.T @ self.x.value


def beliefs_and_truth(I, r):
    rg = np.random.default_rng([2022, r])
    lam = rg.multivariate_normal(I.lam_hat, I.P0L)
    alpha = rg.choice(m022.BSW[0], size=I.N, p=m022.BSW[1]) + I.delta
    zf = rg.standard_normal((I.T, I.K)) @ np.linalg.cholesky(I.Sf).T
    zA = rg.standard_normal((I.T, I.N)) * I.sdA
    m = I.m0.copy(); ms = []
    for t in range(I.T):
        ms.append(m.copy())
        f = lam + zf[t]; yA = alpha + zA[t]
        m = np.concatenate([m[:I.N] + I.KA[t] @ (yA - m[:I.N]), m[I.N:] + I.KL[t] @ (f - m[I.N:])])
    theta = np.concatenate([alpha, lam])
    return ms, theta @ I.G.T + I.g0, alpha


def equal_weight(I):
    """Deviation 1: the largest common weight w with 38 w + C(w 1 - x_inc) <= 1 (full 1/38 violates the budget once
    the first trade's cost is paid)."""
    lo, hi = 0.0, 1.0 / I.n
    for _ in range(60):
        w = (lo + hi) / 2
        u = w - I.x_inc
        if I.n * w + 0.5 * np.sum(I.Lam * u * u) <= 1:
            lo = w
        else:
            hi = w
    return np.full(I.n, lo)


def path_task(args):
    part, delta, r, policies, H = args
    I = inst(delta)
    ms, mu_true, alpha = beliefs_and_truth(I, r)
    key = (part, delta, H)
    progs = _PROGS.setdefault(key, {})
    T, N = I.T, I.N
    out = {}
    extra = {}
    for p in policies:
        x_prev = I.x_inc.copy()
        ce = 0.0; zero_f = np.zeros(N); zero_e = np.zeros(I.M); inact_f = inact_e = 0.0; invested = 0.0; bind = 0
        half_f, half_e = [], []
        for t in range(T):
            h = min(H, T - t)
            mu = I.G @ ms[t] + I.g0
            if p in ("MPC-L", "MPC-S", "ETF-only", "prop-L"):
                kk = (p, h)
                if kk not in progs:
                    progs[kk] = Program(I, h, cost="prop" if p == "prop-L" else "quad",
                                        frozen=np.arange(N) if p == "ETF-only" else None)
                Ls = [I.Lchol[t + k] if p != "MPC-S" else I.Lchol[t] for k in range(h)]
                x = progs[kk].solve(x_prev, mu, Ls)
            elif p == "myopic":
                if "myopic" not in progs:
                    progs["myopic"] = Program(I, 1)
                x = progs["myopic"].solve(x_prev, mu, [I.Lr])
            elif p == "two-stage":
                if "s1" not in progs:
                    progs["s1"] = Stage1(I); progs["s2"] = Program(I, 1, fibre=True)
                Lf = np.linalg.cholesky(I.Sf + I.PL[t])
                b = progs["s1"].solve(x_prev, ms[t][N:], Lf)
                x = progs["s2"].solve(x_prev, mu, [I.Lchol[t]], b)
            elif p == "equal":
                x = equal_weight(I) if t == 0 else x_prev
            else:
                x = x_prev.copy()
            u = x - x_prev
            cost = 0.5 * np.sum(I.Lam * u * u) if p != "prop-L" else \
                np.sum(np.concatenate([np.full(N, KAPPA[0]), np.full(I.M, KAPPA[1])]) * np.abs(u))
            ce += x @ mu_true - 0.5 * I.gamma * x @ I.Sigma_r @ x - cost
            zero_f += x[:N] <= 1e-6; zero_e += x[N:] <= 1e-6
            inact_f += np.mean(np.abs(u[:N]) < 1e-5); inact_e += np.mean(np.abs(u[N:]) < 1e-5)
            invested += x.sum(); bind += (x.sum() + cost >= 1 - 1e-6)
            if p == "prop-L":
                if "fric" not in progs:
                    progs["fric"] = Program(I, 1, zero_cost=True)
                xh = progs["fric"].solve(x_prev, mu, [I.Lchol[t]])
                nt = np.abs(u) < 1e-5
                d = np.abs(x_prev - xh)
                half_f += list(d[:N][nt[:N]]); half_e += list(d[N:][nt[N:]])
            x_prev = x
        out[p] = ce / T
        extra[p] = dict(zero_funds=(zero_f / T).tolist(), zero_etfs=(zero_e / T).tolist(), inaction_funds=inact_f / T,
                        inaction_etfs=inact_e / T, invested=invested / T, budget_binding=bind / T,
                        half_f=half_f if p == "prop-L" else None, half_e=half_e if p == "prop-L" else None)
    return r, out, extra


_PROGS = {}


def run_part(part, delta, R, policies, H=4, r0=0):
    tasks = [(part, delta, r, policies, H) for r in range(r0, r0 + R)]
    with Pool(int(os.environ.get("PROCS", "9"))) as pool:
        res = pool.map(path_task, tasks, chunksize=10)
    return res


def main():
    part = sys.argv[1] if len(sys.argv) > 1 else "main"
    t0 = time.time()
    if part == "main":
        R, res = 2000, run_part("main", 0.0, 2000, POLICIES)
        while True:
            ce = {p: np.array([x[1][p] for x in res]) for p in POLICIES}
            se = max(np.std(ce["MPC-L"] - ce[p], ddof=1) / np.sqrt(len(res)) * 1e4 for p in POLICIES if p != "MPC-L")
            if se <= 0.1 or len(res) >= 8000:
                break
            res += run_part("main", 0.0, 2000, POLICIES, r0=len(res))
        payload = res
    elif part == "h8":
        payload = run_part("h8", 0.0, 2000, ["MPC-L"], H=8)
    elif part == "sens":
        payload = {str(d): run_part("sens", d, 1000, POLICIES) for d in (0.0019, 0.0024)}   # mean 0 and +0.05%
    elif part == "prop":
        payload = run_part("prop", 0.0, 2000, ["prop-L"])
    (HERE / f"{part}.json").write_text(json.dumps(dict(part=part, seconds=time.time() - t0, rows=payload)))
    print(f"{part}: seconds {time.time() - t0:.0f}")


if __name__ == "__main__":
    main()
