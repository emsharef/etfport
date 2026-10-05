"""Experiment 049: claim 045 (D16's second claim; math/claim045-d16-bounds-text at 919441d4) against the validated
two-review harness. Registered design: experiments/049-claim045-bounds-check.md.  Run: uv run python experiments/049/run.py
"""
import importlib.util
import itertools
import json
import multiprocessing as mp
import sys
import time
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "d16-harness"))
from harness import Model  # noqa: E402,F401

_e = importlib.util.spec_from_file_location("run047", HERE.parent / "047" / "run.py"); E47 = importlib.util.module_from_spec(_e); _e.loader.exec_module(E47)
_f = importlib.util.spec_from_file_location("run048", HERE.parent / "048" / "run.py"); E48 = importlib.util.module_from_spec(_f); _f.loader.exec_module(E48)
TOL_X, HSLACK, TAU = 1e-7, 1e-6, 1e-7


class LP:
    """Experiment 047's multiplier LP in (eta_0, eta_1[k], sigma_0[i], sigma_1[k][i], tau), built once; `root` includes
    today's lines (claim 044 part 2) or only tomorrow's (the multiplier sets of claim 044 3(c))."""

    def __init__(self, M, x0m, x0, h0p, nodes, x1, h1p, root=True):
        self.M, self.nodes = M, nodes; K = len(nodes); self.K = K
        kp = np.array([M.kAp, M.kEp]); km = np.array([M.kAm, M.kEm]); cap = np.array([M.capA, np.inf])
        n = 1 + K + 2 + 2 * K + 1; self.n = n; iT = n - 1; self.iT = iT
        self.e0 = 0; self.e1 = lambda k: 1 + k; self.s0 = lambda i: 1 + K + i; self.s1 = lambda k, i: 1 + K + 2 + 2 * k + i
        A, b = [], []
        def le(row, rhs):
            r = row.copy(); r[iT] -= 1; A.append(r); b.append(rhs)
        def eq(row, rhs):
            le(row, rhs); le(-row, -rhs)
        def slope(idx, ecoef, u, i):
            if u > TOL_X:
                r = np.zeros(n); r[idx] = 1; r -= kp[i] * ecoef; eq(r, kp[i])
            elif u < -TOL_X:
                r = np.zeros(n); r[idx] = 1; r += km[i] * ecoef; eq(r, -km[i])
            else:
                r = np.zeros(n); r[idx] = 1; r -= kp[i] * ecoef; le(r, kp[i])
                r = np.zeros(n); r[idx] = -1; r -= km[i] * ecoef; le(r, km[i])
        def line(row, const, xi, i):
            at0, atc = xi <= TOL_X, xi >= cap[i] - TOL_X
            if at0 and not atc:
                le(row, -const)
            elif atc and not at0:
                le(-row, const)
            else:
                eq(row, -const)
        beta = M.beta; eh = np.zeros(n); eh[self.e0] = 1
        for k, nd in enumerate(nodes):
            eh[self.e1(k)] += beta * nd["prob"]
            mu, S = M.moments(1, nd["m"]); g1 = mu - M.gamma * S @ x1[k]; xm1 = x0 * nd["g"]
            ek = np.zeros(n); ek[self.e1(k)] = 1
            for i in range(2):
                slope(self.s1(k, i), ek, x1[k][i] - xm1[i], i)
                row = np.zeros(n); row[self.e1(k)] = -1; row[self.s1(k, i)] = -1
                line(row, g1[i], x1[k][i], i)
        mu0, S0 = M.moments(0, M.m0); self.g0 = mu0 - M.gamma * S0 @ x0
        if root:
            for i in range(2):
                slope(self.s0(i), eh, x0[i] - x0m[i], i)
                row = -eh.copy(); row[self.s0(i)] -= 1
                for k, nd in enumerate(nodes):
                    row[self.e1(k)] += beta * nd["prob"] * nd["g"][i]; row[self.s1(k, i)] += beta * nd["prob"] * nd["g"][i]
                line(row, self.g0[i], x0[i], i)
        self.A, self.b = np.array(A), np.array(b)
        self.bounds = [(0, 0 if (h0p > HSLACK or not root) else None)] + [(0, 0 if h1p[k] > HSLACK else None) for k in range(K)] + [(None, None)] * (2 + 2 * K) + [(0, None)]
        self.q = np.array([nd["prob"] for nd in nodes]); self.G = np.array([nd["g"] for nd in nodes]); self.kp, self.km = kp, km

    def S(self, i):
        """S_i = beta sum_k q_k g_{k,i} (eta_1[k] + sigma_1[k][i]) as a linear form."""
        c = np.zeros(self.n)
        for k in range(self.K):
            c[self.e1(k)] += self.M.beta * self.q[k] * self.G[k, i]; c[self.s1(k, i)] += self.M.beta * self.q[k] * self.G[k, i]
        return c

    def Eeta1(self):
        c = np.zeros(self.n)
        for k in range(self.K):
            c[self.e1(k)] = self.q[k]
        return c

    def solve(self, c=None, extra_bounds=None, tau_cap=None, sense=1):
        bounds = list(self.bounds)
        for j, bd in (extra_bounds or {}).items():
            lo, hi = bounds[j]; bounds[j] = (max(lo, bd[0]) if bd[0] is not None else lo, (min(hi, bd[1]) if hi is not None else bd[1]) if bd[1] is not None else hi)
        if c is None:
            cc = np.zeros(self.n); cc[self.iT] = 1
        else:
            cc = sense * c; bounds[self.iT] = (0, tau_cap)
        res = linprog(cc, A_ub=self.A, b_ub=self.b, bounds=bounds, method="highs")
        return res


def eta_bar_need(M, nodes, x0, h0p):
    kp = np.array([M.kAp, M.kEp]); eb, need = [], []
    for nd in nodes:
        mu, S = M.moments(1, nd["m"])
        eb.append(float(max(np.maximum(mu - kp, 0) / (1 + kp))))
        xhat = np.maximum(mu - kp, 0) / (M.gamma * np.diag(S)); xhat[0] = min(xhat[0], np.inf)
        need.append(float(np.sum((1 + kp) * np.maximum(xhat - nd["g"] * x0, 0))))
    return np.array(eb), np.array(need)


def parts123(M, x0m, h0, tag):
    D = M.solve(x0m, h0, T=2); nodes = D["levels"][1]; x0 = D["x"][0][0]; x1 = D["x"][1]; h0p = D["h"][0][0]; h1p = D["h"][1]
    rec = dict(tag=tag)
    eb, need = eta_bar_need(M, nodes, x0, h0p)
    Lt = LP(M, x0m, x0, h0p, nodes, x1, h1p, root=False)
    base = Lt.solve(); rec["tom_tau"] = float(base.fun) if base.status == 0 else None
    # 1(a)/(c): eta_1 <= eta_bar jointly
    r1 = Lt.solve(extra_bounds={Lt.e1(k): (None, eb[k]) for k in range(Lt.K)}); rec["p1a_tau"] = float(r1.fun) if r1.status == 0 else None
    # 1(b): eta_1 = 0 where the need is covered
    cov = [k for k in range(Lt.K) if h0p >= need[k]]
    r2 = Lt.solve(extra_bounds={Lt.e1(k): (None, 0.0) for k in cov}); rec["p1b_tau"] = float(r2.fun) if r2.status == 0 else None
    rec["p1b_states"] = len(cov); rec["p1_all_covered"] = len(cov) == Lt.K
    # with today's lines: the joint LP with the selection, and eta_hat_0's bounds
    Lr = LP(M, x0m, x0, h0p, nodes, x1, h1p, root=True)
    r3 = Lr.solve(extra_bounds={Lr.e1(k): (None, eb[k]) for k in range(Lr.K)})
    if r3.status == 0:
        z = r3.x; etah = z[Lr.e0] + M.beta * Lt.q @ np.array([z[Lr.e1(k)] for k in range(Lr.K)])
        rec.update(p1c_tau=float(r3.fun), p1c_lo=float(z[Lr.e0] - etah), p1c_hi=float(etah - z[Lr.e0] - M.beta * Lt.q @ eb))
    # part 2: brackets and sign conditions at the extremes of the admissible (tomorrow) set, with the selection
    ext = {Lt.e1(k): (None, eb[k]) for k in range(Lt.K)}
    viol = []; signs = []
    for i in range(2):
        cS = Lt.S(i); cE = Lt.Eeta1(); cR = cS - M.beta * (1 + Lt.kp[i]) * cE
        for c in (cS, cR):
            for sense in (1, -1):
                r = Lt.solve(c=c, extra_bounds=ext, tau_cap=TAU, sense=sense)
                if r.status != 0:
                    continue
                z = r.x; e1 = np.array([z[Lt.e1(k)] for k in range(Lt.K)]); Si = cS @ z; Ri = cR @ z
                g = Lt.G[:, i]; Eg = Lt.q @ g
                lo_S, hi_S = -M.beta * Eg * Lt.km[i], M.beta * Lt.q @ (g * (e1 + (1 + e1) * Lt.kp[i]))
                lo_R = M.beta * (Lt.q @ (e1 * (g * (1 - Lt.km[i]) - 1 - Lt.kp[i])) - Lt.km[i] * Eg)
                hi_R = M.beta * (Lt.q @ (e1 * (g - 1)) * (1 + Lt.kp[i]) + Lt.kp[i] * Eg)
                viol.append(max(lo_S - Si, Si - hi_S, lo_R - Ri, Ri - hi_R))
                hoard = (Lt.q @ (e1 * (g - 1))) * (1 + Lt.kp[i]) < -Lt.kp[i] * Eg - 1e-12
                front = Lt.q @ (e1 * (g * (1 - Lt.km[i]) - 1 - Lt.kp[i])) > Lt.km[i] * Eg + 1e-12
                if hoard:
                    signs.append(dict(i=i, cond="hoard", R=float(Ri), ok=bool(Ri < 1e-12)))
                if front:
                    signs.append(dict(i=i, cond="front", R=float(Ri), ok=bool(Ri > -1e-12)))
    rec["p2_viol"] = float(max(viol)) if viol else None; rec["p2_signs"] = signs
    # part 3: myopic optimality and interior trades today
    mu0, S0 = M.moments(0, M.m0); xmy, emy0, hmy = E47.one_review(M, mu0, S0, x0m, h0)
    x1my, h1my = [], []
    for nd in nodes:
        mu, S = M.moments(1, nd["m"]); xx, ee, hh = E47.one_review(M, mu, S, xmy * nd["g"], hmy); x1my.append(xx); h1my.append(hh)
    q = Lt.q
    opt = bool(np.max(np.abs(xmy - x0)) <= 1e-5 and np.max(np.abs(q @ np.array(x1my) - q @ np.array(x1))) <= 1e-5)
    cap = np.array([M.capA, np.inf]); interior = [i for i in range(2) if abs(xmy[i] - x0m[i]) > TOL_X and TOL_X < xmy[i] < cap[i] - TOL_X]
    rec.update(my_opt=opt, my_interior=interior, my_bind0=bool(hmy < HSLACK), my_eta0=emy0)
    if opt and interior:
        Lm = LP(M, x0m, xmy, hmy, nodes, x1my, h1my, root=False); eq = []
        for i in interior:
            buy = xmy[i] > x0m[i]; cR = Lm.S(i) - M.beta * (1 + Lm.kp[i] if buy else 1 - Lm.km[i]) * Lm.Eeta1()
            lo = Lm.solve(c=cR, tau_cap=TAU, sense=1); hi = Lm.solve(c=cR, tau_cap=TAU, sense=-1)
            rng = (float(cR @ lo.x) if lo.status == 0 else None, float(cR @ hi.x) if hi.status == 0 else None)
            eq.append(dict(i=i, buy=bool(buy), range=rng, holds=bool(rng[0] is not None and rng[0] <= 1e-9 and rng[1] >= -1e-9)))
        rec["p3_eq"] = eq
    return rec


def part4(i):
    M, x0m, h0 = E47.instance(i, costless=True)
    D = M.solve(x0m, h0, T=2); x0 = D["x"][0][0]
    mu0, S0 = M.moments(0, M.m0); xmy, emy0, hmy = E47.one_review(M, mu0, S0, x0m, h0)
    rec = dict(i=i)
    buys = xmy[0] - x0m[0] > TOL_X and TOL_X < xmy[0] < M.capA - TOL_X
    R = M.solve(x0m, h0, T=2, fix_root_fund=float(xmy[0])); xr = R["x"][0][0]
    hyp = bool(buys and hmy > HSLACK and R["h"][0][0] > HSLACK and x0[1] > 1e-6 and xr[1] > 1e-6)
    rec["hyp"] = hyp
    if not hyp:
        return rec
    nodes = R["levels"][1]
    L = LP(M, x0m, xr, R["h"][0][0], nodes, R["x"][1], R["h"][1], root=False)
    rho0 = S0[0, 1] / S0[1, 1]
    cA = L.S(0) - M.beta * (1 + M.kAp) * L.Eeta1(); cE = L.S(1) - M.beta * L.Eeta1()
    c = cA - rho0 * cE
    lo = L.solve(c=c, tau_cap=TAU, sense=1); hi = L.solve(c=c, tau_cap=TAU, sense=-1)
    vlo = float(c @ lo.x) if lo.status == 0 else None; vhi = float(c @ hi.x) if hi.status == 0 else None
    d = float(x0[0] - xmy[0])
    rec.update(range=(vlo, vhi), diff=d, unique=bool(vlo is not None and abs(vhi - vlo) < 1e-9))
    if vlo is not None and vhi is not None and (vlo > 1e-9 or vhi < -1e-9):
        rec["pred"] = 1 if vlo > 1e-9 else -1
        rec["ok"] = bool(np.sign(d) == rec["pred"]) if abs(d) > 1e-5 else None
    return rec


def run_a(i):
    M, x0m, h0 = E47.instance(i)
    r = parts123(M, x0m, h0, f"047 main {i}"); return r


def run_b(args):
    regime, start, cash, unc, costmul = args
    M = E48.model(regime, unc, costmul)
    return parts123(M, np.array(start, float), cash, f"048 {regime} {start} {cash} {unc} {costmul}")


def main():
    t0 = time.time()
    cells = list(itertools.product(("equity-style", "fixed-income-style"), ((0.0, 0.9), (0.15, 0.0), (0.075, 0.45)), (1.0, 0.005), (1.0, 3.0), (0.2, 1.0, 5.0)))
    with mp.Pool(8) as pool:
        a = pool.map(run_a, range(300), chunksize=4)
        b = pool.map(run_b, cells, chunksize=2)
        c = pool.map(part4, range(3000), chunksize=8)          # Deviation 2: part 4 extended from 300 to 3,000 draws
    S = dict(main047=a, cells048=b, part4=c, seconds=time.time() - t0, statement="claim 045 at 919441d4 (math/claim045-d16-bounds-text)")
    json.dump(S, open(HERE / "summary.json", "w"), separators=(",", ":"), default=lambda o: o.tolist() if hasattr(o, "tolist") else (bool(o) if isinstance(o, np.bool_) else float(o)))
    print("done", S["seconds"])


if __name__ == "__main__":
    main()
