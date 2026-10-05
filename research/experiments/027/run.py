"""Experiment 027: regime map (AGENTS.md rule 22). Registered design: experiments/027-regime-map.md.

Reduced M5 instance with persistence (experiment 025's filter) in the funded long-only space (024's constraints,
fund caps 0.25, ETF caps 1). Factors: Mkt-RF, SMB, HML from the pinned French five-factor file (experiment 022's
loader). Every other input is an assumption, set per cell. Policies are per-quarter convex programs (CLARABEL).
Run:    uv run python experiments/027/run.py            (all 88 cells; writes raw_<cell>.json per cell)
        uv run python experiments/027/run.py summary    (writes summary.json)
Report: uv run python experiments/027/report.py
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

GAMMA, T, R, N, K = 5.0, 20, 500, 6, 3
ETF_FULL = np.array([[1, 0, 0], [1, 0.8, 0.2], [1, 0, 0.6]], float)
SD_ETF, CAP_F, CAP_E = 0.003, 0.25, 1.0
ANCHORS = {
    "EQ": dict(a=-0.19, s=0.35, sA=2.0, r=10.0, lamE=0.01, rho=1.0, f=1.0, D=1.0, menu="full"),
    "FI": dict(a=0.20, s=0.35, sA=1.0, r=0.5, lamE=0.1, rho=1.0, f=10.0, D=1.0, menu="missing"),
}
STARTS = ["all-ETF", "all-fund", "mixed"]
POLICIES = ["MPC-L", "MPC-S", "rule", "ETF-only", "funds-only", "two-stage"]


def cells():
    out = []
    for anc, base in ANCHORS.items():
        for a in (-0.4, -0.2, 0.0, 0.2, 0.4):
            for r in (0.5, 1.0, 2.0, 10.0):
                out.append(("S1", anc, dict(base, a=a, r=r)))
        for ratio in (0.05, 0.175, 0.5, 1.0):
            for rho in (0.5, 0.95, 1.0):
                out.append(("S2", anc, dict(base, sA=base["s"] / ratio, rho=rho)))
        for menu in ("full", "missing"):
            for D in (1.0, 4.0, 16.0):
                out.append(("S3", anc, dict(base, menu=menu, D=D)))
        for f in (1.0, 10.0, 30.0):
            for lamE in (0.01, 0.1):
                out.append(("S4", anc, dict(base, f=f, lamE=lamE)))
    return out


_FF = {}


def factors():
    if "q" not in _FF:
        q = m022.ff5_quarterly()[["MktRF", "SMB", "HML"]]
        _FF["q"] = (q.mean().to_numpy(), q.cov().to_numpy(), len(q))
    return _FF["q"]


class Inst:
    def __init__(self, p):
        lam_hat, Sf, nq = factors()
        rng = np.random.default_rng(2027)
        BA = np.column_stack([rng.uniform(0.85, 1.15, N), rng.normal(0, 0.3, (N, 2))])
        BE = ETF_FULL if p["menu"] == "full" else ETF_FULL[:2]
        self.N, self.K, self.M = N, K, len(BE)
        self.n = N + self.M
        self.B = np.vstack([BA, BE])
        self.Sf, self.lam_hat = Sf, lam_hat
        self.sA = p["sA"] / 100
        self.D = np.concatenate([np.full(N, self.sA ** 2), np.full(self.M, SD_ETF ** 2)])
        self.Sigma_r = self.B @ Sf @ self.B.T + np.diag(self.D)
        self.cE = np.full(self.M, p["f"] * 1e-4)
        self.g0 = np.concatenate([np.zeros(N), -self.cE])
        self.G = np.hstack([np.vstack([np.eye(N), np.zeros((self.M, N))]), self.B])
        self.Lam = np.concatenate([np.full(N, p["r"] * p["lamE"]), np.full(self.M, p["lamE"])])
        self.caps = np.concatenate([np.full(N, CAP_F), np.full(self.M, CAP_E)])
        s, sbar = p["s"] / 100, p["s"] / 500
        self.P0A = sbar ** 2 * np.ones((N, N)) + (s ** 2 - sbar ** 2) * np.eye(N)
        self.P0L = p["D"] * Sf / nq
        self.theta_bar = np.concatenate([np.full(N, p["a"] / 100), lam_hat])
        self.m0 = self.theta_bar.copy()
        rho = p["rho"]
        self.Phi = np.concatenate([np.full(N, rho), np.ones(K)])
        Q = np.zeros((N + K, N + K)); Q[:N, :N] = (1 - rho ** 2) * self.P0A
        self.cholQ = np.zeros_like(Q)                                     # Deviation 2: factor the alpha block only
        if rho < 1:
            self.cholQ[:N, :N] = np.linalg.cholesky(Q[:N, :N])
        P0 = np.zeros((N + K, N + K)); P0[:N, :N] = self.P0A; P0[N:, N:] = self.P0L
        Hinfo = np.zeros_like(P0); Hinfo[:N, :N] = np.diag(1 / self.D[:N]); Hinfo[N:, N:] = np.linalg.inv(Sf)
        Ps, Ks, P = [P0], [], P0
        for t in range(T + 8):
            Pu = np.linalg.inv(np.linalg.inv(P) + Hinfo)
            Ks.append(Pu @ Hinfo)
            P = np.diag(self.Phi) @ Pu @ np.diag(self.Phi) + Q
            Ps.append(P)
        self.P, self.Kg = Ps, Ks
        self.Lchol = [np.linalg.cholesky(self.G @ Ps[t] @ self.G.T + self.Sigma_r) for t in range(T + 8)]
        self.starts = {"all-ETF": np.concatenate([np.zeros(N), [0.9], np.zeros(self.M - 1)]),
                       "all-fund": np.concatenate([np.full(N, 0.15), np.zeros(self.M)]),
                       "mixed": np.concatenate([np.full(N, 0.075), [0.45], np.zeros(self.M - 1)])}

    def forecasts(self, m, h):
        return [self.G @ (self.Phi ** k * m + (1 - self.Phi ** k) * self.theta_bar) + self.g0 for k in range(h)]


class Program:
    def __init__(self, I, H, mode=None, fibre=False):
        n = I.n
        self.H = H
        self.xp = cp.Parameter(n); self.mu = [cp.Parameter(n) for _ in range(H)]
        self.L = [cp.Parameter((n, n)) for _ in range(H)]
        self.x = [cp.Variable(n) for _ in range(H)]
        self.b = cp.Parameter(I.K) if fibre else None
        obj, cons, prev = 0, [], self.xp
        for k in range(H):
            u = self.x[k] - prev
            C = 0.5 * cp.sum(cp.multiply(I.Lam, cp.square(u)))
            obj += self.mu[k] @ self.x[k] - 0.5 * GAMMA * cp.sum_squares(self.L[k].T @ self.x[k]) - C
            cons += [self.x[k] >= 0, self.x[k] <= I.caps, cp.sum(self.x[k]) + C <= 1]
            if mode == "etf-only":
                cons += [u[:I.N] <= 0]
            elif mode == "funds-only":
                cons += [u[I.N:] <= 0]
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
        self.xp = cp.Parameter(I.n); self.muf = cp.Parameter(I.K); self.Lf = cp.Parameter((I.K, I.K))
        self.x = cp.Variable(I.n)
        C = 0.5 * cp.sum(cp.multiply(I.Lam, cp.square(self.x - self.xp)))
        b = I.B.T @ self.x
        self.prob = cp.Problem(cp.Maximize(self.muf @ b - 0.5 * GAMMA * cp.sum_squares(self.Lf.T @ b)),
                               [self.x >= 0, self.x <= I.caps, cp.sum(self.x) + C <= 1])
        self.B = I.B

    def solve(self, xp, muf, Lf):
        self.xp.value = xp; self.muf.value = muf; self.Lf.value = Lf
        self.prob.solve(solver="CLARABEL")
        return self.B.T @ self.x.value


class Policies:
    def __init__(self, I):
        self.I = I
        self.progs = {}

    def prog(self, key, *args, **kw):
        if key not in self.progs:
            self.progs[key] = Program(self.I, *args, **kw)
        return self.progs[key]

    def act(self, p, t, x_prev, m):
        I = self.I
        mu_t = I.G @ m + I.g0
        if p == "rule":
            return self.prog(("rule",), 1).solve(x_prev, [mu_t], [I.Lchol[t]])
        if p == "two-stage":
            if "s1" not in self.progs:
                self.progs["s1"] = Stage1(I)
            b = self.progs["s1"].solve(x_prev, m[N:], np.linalg.cholesky(I.Sf + I.P[t][N:, N:]))
            return self.prog(("s2",), 1, fibre=True).solve(x_prev, [mu_t], [I.Lchol[t]], b)
        h = min(8, T - t)
        mode = {"ETF-only": "etf-only", "funds-only": "funds-only"}.get(p)
        Ls = [I.Lchol[t]] * h if p == "MPC-S" else [I.Lchol[t + k] for k in range(h)]
        return self.prog((mode, h), h, mode=mode).solve(x_prev, I.forecasts(m, h), Ls)


def run_path(I, pol, idx, r, start):
    rg = np.random.default_rng([2027, idx, r])
    lam = rg.multivariate_normal(I.lam_hat, I.P0L)
    alpha = rg.multivariate_normal(I.theta_bar[:N], I.P0A)          # Deviation 1: drawn from the pooled prior itself
    zf = rg.standard_normal((T, K)) @ np.linalg.cholesky(I.Sf).T
    zA = rg.standard_normal((T, N)) * I.sA
    eta = rg.standard_normal((T, N + K)) @ I.cholQ.T
    theta = np.concatenate([alpha, lam])
    m = I.m0.copy()
    ms, mus = [], []
    for t in range(T):
        ms.append(m.copy()); mus.append(I.G @ theta + I.g0)
        y = np.concatenate([theta[:N] + zA[t], theta[N:] + zf[t]])
        mp = m + I.Kg[t] @ (y - m)
        m = I.Phi * mp + (1 - I.Phi) * I.theta_bar
        theta = I.Phi * theta + (1 - I.Phi) * I.theta_bar + eta[t]
    out = {}
    held = {}
    for p in POLICIES:
        x = I.starts[start].copy(); ce = 0.0; hq = 0.0
        for t in range(T):
            xn = pol.act(p, t, x, ms[t])
            u = xn - x
            ce += xn @ mus[t] - 0.5 * GAMMA * xn @ I.Sigma_r @ xn - 0.5 * np.sum(I.Lam * u * u)
            hq += np.mean(xn[:N] > 1e-3)
            x = xn
        out[p] = ce / T; held[p] = hq / T
    return out, held


def first_quarter(I, pol):
    """Deterministic t = 0 quantities (common beliefs at t = 0): first-quarter holdings per policy and start, and
    criterion (d): the rule's fund holdings under +-1 prior SD premium beliefs along each factor."""
    res = {}
    for st in STARTS:
        x0 = I.starts[st]
        res[st] = {p: pol.act(p, 0, x0, I.m0).tolist() for p in POLICIES}
    d = 0.0
    base = np.array(res["mixed"]["rule"])[:N]
    for k in range(K):
        for sgn in (-1, 1):
            m = I.m0.copy(); m[N + k] += sgn * np.sqrt(I.P0L[k, k])
            xa = pol.act("rule", 0, I.starts["mixed"], m)[:N]
            d = max(d, float(np.abs(xa - base).sum()))
    res["premium_sensitivity_L1"] = d
    return res


def cell_task(args):
    idx, slice_, anc, p = args
    t0 = time.time()
    I = Inst(p); pol = Policies(I)
    fq = first_quarter(I, pol)
    rows = {st: [run_path(I, pol, idx, r, st) for r in range(R)] for st in STARTS}
    out = dict(idx=idx, slice=slice_, anchor=anc, params=p, first_quarter=fq,
               ce={st: {q: [x[0][q] for x in rows[st]] for q in POLICIES} for st in STARTS},
               held={st: {q: float(np.mean([x[1][q] for x in rows[st]])) for q in POLICIES} for st in STARTS},
               seconds=time.time() - t0)
    (HERE / f"raw_{idx:02d}.json").write_text(json.dumps(out))
    return idx, time.time() - t0


def main():
    if sys.argv[1:] == ["summary"]:
        allc = [json.load(open(f)) for f in sorted(HERE.glob("raw_*.json"))]
        for c in allc:     # compact: certainty equivalents in bp, rounded to 1e-4 bp (far below every SE)
            c["ce_bp"] = {st: {q: [round(v * 1e4, 4) for v in vs] for q, vs in d.items()} for st, d in c.pop("ce").items()}
        (HERE / "summary.json").write_text(json.dumps(allc, separators=(",", ":")))
        print(f"wrote summary.json ({len(allc)} cells)")
        return
    C = cells()
    todo = [(i, s, a, p) for i, (s, a, p) in enumerate(C) if not (HERE / f"raw_{i:02d}.json").exists()]
    with Pool(int(os.environ.get("PROCS", "9"))) as pool:
        for idx, sec in pool.imap_unordered(cell_task, todo):
            print(f"cell {idx} done in {sec:.0f} s", flush=True)


if __name__ == "__main__":
    main()
