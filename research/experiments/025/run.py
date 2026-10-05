"""Experiment 025: persistent alpha and premia in experiment 024's implementable space.
Registered design: experiments/025-m5-persistence-value.md.

Experiment 022's calibrated instance (experiments/022/model.py) and 024's constraints (long-only, funded
1'x + C(u) <= 1, fund caps 0.10, ETF caps 1, quadratic costs). New here: M5's state dynamics
theta_{t+1} = Phi theta_t + (I - Phi) theta_bar + eta, eta ~ N(0, Q), with Phi = diag(rho_A I_N, rho_L I_K) and
Q = (1 - rho^2) P_0 per block (rho = 1: fixed, Q = 0). Filter: update P+ = (P^-1 + Hinfo)^-1, m+ = m + P+ Hinfo (y - m)
(alpha from r^A - B^A f, lambda from f; the blocks decouple), then predict m' = Phi m+ + (I - Phi) theta_bar,
P' = Phi P+ Phi + Q. Predictive moments of quarter t: mu_t = G m_t + g0, Sigma_t = G P_t G' + Sigma_r.
Run:    uv run python experiments/025/run.py <cell>      (cells: A50 A80 A95 L50 L80 L95 B80; writes raw_<cell>.json)
        uv run python experiments/025/run.py summary     (writes summary.json from the raw files)
Report: uv run python experiments/025/report.py
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
CELLS = {"A50": (0.50, 1.0), "A80": (0.80, 1.0), "A95": (0.95, 1.0), "L50": (1.0, 0.50), "L80": (1.0, 0.80),
         "L95": (1.0, 0.95), "B80": (0.80, 0.80)}
POLICIES = ["MPC-L8", "MPC-L4", "MPC-S8", "MPC-flat8", "myopic", "ETF-only8", "two-stage"]
_I = {}


def inst(cell):
    if cell in _I:
        return _I[cell]
    rA, rL = CELLS[cell]
    I = m022.Inst()
    N, K = I.N, I.K
    I.caps = np.concatenate([np.full(N, CAP_FUND), np.full(I.M, CAP_ETF)])
    I.Phi = np.concatenate([np.full(N, rA), np.full(K, rL)])
    P0 = np.zeros((N + K, N + K)); P0[:N, :N] = I.P0A; P0[N:, N:] = I.P0L
    Q = np.zeros_like(P0)
    Q[:N, :N] = (1 - rA ** 2) * I.P0A
    Q[N:, N:] = (1 - rL ** 2) * I.P0L
    I.Qeta = Q
    I.cholQ = np.linalg.cholesky(Q + 1e-30 * np.eye(N + K)) if np.any(Q) else np.zeros_like(Q)
    I.theta_bar = I.m0.copy()
    Hinfo = np.zeros_like(P0); Hinfo[:N, :N] = np.diag(1 / I.DA); Hinfo[N:, N:] = np.linalg.inv(I.Sf)
    Ps, Pp, Ks = [P0], [], []
    P = P0
    for t in range(I.T + 8):
        Pu = np.linalg.inv(np.linalg.inv(P) + Hinfo) if np.all(np.diag(P) > 0) else P - P @ Hinfo @ P
        Pp.append(Pu); Ks.append(Pu @ Hinfo)
        P = np.diag(I.Phi) @ Pu @ np.diag(I.Phi) + Q
        Ps.append(P)
    I.Ppred, I.Kgain = Ps, Ks
    I.Lchol = [np.linalg.cholesky(I.G @ Ps[t] @ I.G.T + I.Sigma_r) for t in range(I.T + 8)]
    I.Lr = np.linalg.cholesky(I.Sigma_r)
    I.PLpred = [Ps[t][N:, N:] for t in range(I.T + 8)]
    _I[cell] = I
    return I


class Program:
    """max sum_k x_k'mu_k - (gamma/2)|L_k'x_k|^2 - (1/2) u_k'Lam u_k s.t. the constraints; parameters x_prev, mu_k, L_k."""

    def __init__(self, I, H, frozen=None, fibre=False):
        n = I.n
        self.H = H
        self.xp = cp.Parameter(n)
        self.mu = [cp.Parameter(n) for _ in range(H)]
        self.L = [cp.Parameter((n, n)) for _ in range(H)]
        self.x = [cp.Variable(n) for _ in range(H)]
        self.b = cp.Parameter(I.K) if fibre else None
        obj, cons, prev = 0, [], self.xp
        for k in range(H):
            u = self.x[k] - prev
            C = 0.5 * cp.sum(cp.multiply(I.Lam, cp.square(u)))
            obj += self.mu[k] @ self.x[k] - 0.5 * I.gamma * cp.sum_squares(self.L[k].T @ self.x[k]) - C
            cons += [self.x[k] >= 0, self.x[k] <= I.caps, cp.sum(self.x[k]) + C <= 1]
            if frozen is not None:
                cons += [self.x[k][frozen] == self.xp[frozen]]
            prev = self.x[k]
        if fibre:
            cons += [I.B.T @ self.x[0] == self.b]
        self.prob = cp.Problem(cp.Maximize(obj), cons)

    def solve(self, xp, mus, Ls, b=None):
        self.xp.value = xp
        for k in range(self.H):
            self.mu[k].value = mus[k]; self.L[k].value = Ls[k]
        if b is not None:
            self.b.value = b
        self.prob.solve(solver="CLARABEL")
        if self.prob.status not in ("optimal", "optimal_inaccurate"):
            raise RuntimeError(self.prob.status)
        return np.clip(self.x[0].value, 0.0, None)


class Stage1:
    def __init__(self, I):
        n = I.n
        self.xp = cp.Parameter(n); self.muf = cp.Parameter(I.K); self.Lf = cp.Parameter((I.K, I.K))
        self.x = cp.Variable(n)
        C = 0.5 * cp.sum(cp.multiply(I.Lam, cp.square(self.x - self.xp)))
        b = I.B.T @ self.x
        self.prob = cp.Problem(cp.Maximize(self.muf @ b - 0.5 * I.gamma * cp.sum_squares(self.Lf.T @ b)),
                               [self.x >= 0, self.x <= I.caps, cp.sum(self.x) + C <= 1])
        self.B = I.B

    def solve(self, xp, muf, Lf):
        self.xp.value = xp; self.muf.value = muf; self.Lf.value = Lf
        self.prob.solve(solver="CLARABEL")
        return self.B.T @ self.x.value


def path(I, r):
    """Truth and beliefs on path r: theta_0 and return shocks from 024's stream (2022, r); state innovations from (2025, r)."""
    rg = np.random.default_rng([2022, r])
    lam = rg.multivariate_normal(I.lam_hat, I.P0L)
    alpha = rg.choice(m022.BSW[0], size=I.N, p=m022.BSW[1])
    zf = rg.standard_normal((I.T, I.K)) @ np.linalg.cholesky(I.Sf).T
    zA = rg.standard_normal((I.T, I.N)) * I.sdA
    eta = np.random.default_rng([2025, r]).standard_normal((I.T, I.N + I.K)) @ I.cholQ.T
    theta = np.concatenate([alpha, lam])
    m = I.m0.copy()
    ms, mus_true = [], []
    Phi = I.Phi
    for t in range(I.T):
        ms.append(m.copy()); mus_true.append(I.G @ theta + I.g0)
        y = np.concatenate([theta[:I.N] + zA[t], theta[I.N:] + zf[t]])
        mplus = m + I.Kgain[t] @ (y - m)
        m = Phi * mplus + (1 - Phi) * I.theta_bar
        theta = Phi * theta + (1 - Phi) * I.theta_bar + eta[t]
    return ms, mus_true


_PROGS = {}


def path_task(args):
    cell, r = args
    I = inst(cell)
    ms, mus_true = path(I, r)
    progs = _PROGS.setdefault(cell, {})
    N, T = I.N, I.T
    out = {}
    turn = {}
    for p in POLICIES:
        x_prev = I.x_inc.copy(); ce = 0.0; tf = te = 0.0; zf = 0.0
        for t in range(T):
            mu_t = I.G @ ms[t] + I.g0
            if p == "myopic":
                if "myopic" not in progs:
                    progs["myopic"] = Program(I, 1)
                x = progs["myopic"].solve(x_prev, [mu_t], [I.Lr])
            elif p == "two-stage":
                if "s1" not in progs:
                    progs["s1"] = Stage1(I); progs["s2"] = Program(I, 1, fibre=True)
                b = progs["s1"].solve(x_prev, ms[t][N:], np.linalg.cholesky(I.Sf + I.PLpred[t]))
                x = progs["s2"].solve(x_prev, [mu_t], [I.Lchol[t]], b)
            else:
                Hmax = 4 if p == "MPC-L4" else 8
                h = min(Hmax, T - t)
                key = (p, h)
                if key not in progs:
                    progs[key] = Program(I, h, frozen=np.arange(N) if p == "ETF-only8" else None)
                if p == "MPC-flat8":
                    mus = [mu_t] * h
                else:
                    mus = []
                    for k in range(h):
                        fk = I.Phi ** k
                        mus.append(I.G @ (fk * ms[t] + (1 - fk) * I.theta_bar) + I.g0)
                Ls = [I.Lchol[t]] * h if p == "MPC-S8" else [I.Lchol[t + k] for k in range(h)]
                x = progs[key].solve(x_prev, mus, Ls)
            u = x - x_prev
            ce += x @ mus_true[t] - 0.5 * I.gamma * x @ I.Sigma_r @ x - 0.5 * np.sum(I.Lam * u * u)
            tf += np.abs(u[:N]).sum(); te += np.abs(u[N:]).sum(); zf += np.mean(x[:N] <= 1e-6)
            x_prev = x
        out[p] = ce / T
        turn[p] = (tf / T, te / T, zf / T)
    return r, out, turn


def run_cell(cell, R0, R):
    with Pool(int(os.environ.get("PROCS", "9"))) as pool:
        return pool.map(path_task, [(cell, r) for r in range(R0, R0 + R)], chunksize=10)


def main():
    arg = sys.argv[1]
    if arg == "summary":
        out = {}
        for cell in CELLS:
            d = json.load(open(HERE / f"raw_{cell}.json"))
            rows = d["rows"]
            out[cell] = dict(seconds=d["seconds"], R=len(rows),
                             ce={p: [x[1][p] for x in rows] for p in POLICIES},
                             turnover_funds={p: float(np.mean([x[2][p][0] for x in rows])) for p in POLICIES},
                             turnover_etfs={p: float(np.mean([x[2][p][1] for x in rows])) for p in POLICIES},
                             funds_at_zero={p: float(np.mean([x[2][p][2] for x in rows])) for p in POLICIES})
        (HERE / "summary.json").write_text(json.dumps(out))
        print("wrote summary.json")
        return
    cell = arg
    t0 = time.time()
    rows = run_cell(cell, 0, 2000)
    while len(rows) < 6000:                       # registered: raise R by 2,000 up to 6,000 if SE > 0.1 bp
        d = np.array([x[1]["MPC-L8"] - x[1]["myopic"] for x in rows]) * 1e4
        if d.std(ddof=1) / np.sqrt(len(d)) <= 0.1:
            break
        rows += run_cell(cell, len(rows), 2000)
    (HERE / f"raw_{cell}.json").write_text(json.dumps(dict(cell=cell, seconds=time.time() - t0, rows=rows)))
    print(f"{cell}: R {len(rows)}, seconds {time.time() - t0:.0f}", flush=True)


if __name__ == "__main__":
    main()
