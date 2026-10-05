"""Experiment 034: claim 102 (when a fund is held, bought or sold versus adjusted through ETFs) against an independent
one-review solver (experiment 029's) and, for part 6, an exact one-instrument dynamic program (experiment 023's L1
transform). Registered design: experiments/034-criterion-b-check.md.  Run: uv run python experiments/034/run.py
"""
import importlib.util
import itertools
import json
import multiprocessing as mp
import sys
import time
from pathlib import Path

import cvxpy as cp
import numpy as np
from scipy.optimize import brentq

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("run029", HERE.parent / "029" / "run.py")
m29 = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(m29)
sys.path.insert(0, str(HERE.parent / "023"))
import fastdp  # noqa: E402

Inst, GAMMA, SF, PL, LAM, V, SCALE, INTERIOR = m29.Inst, m29.GAMMA, m29.SF, m29.PL, m29.LAM, m29.V, m29.SCALE, m29.INTERIOR
BA = m29.BA3
BE = np.eye(2)                          # Deviation 1 (experiment 029's Deviation 1)
TRADE = 1e-5
NAMED = {"equity-style": (-0.0019, 0.005, 0.0002), "fixed-income-style": (0.0020, 0.002, 0.005)}   # alpha, fund rate, ETF rate


def opts(s):
    return dict(CLARABEL=dict(tol_gap_abs=1e-12, tol_gap_rel=1e-10, tol_feas=1e-10, max_iter=500),
                OSQP=dict(eps_abs=1e-10, eps_rel=1e-10, polish=True, max_iter=400000))[s]


def solve(I, solver="CLARABEL", fixA=False):
    n = I.n; x, up, um = cp.Variable(n), cp.Variable(n), cp.Variable(n)
    cons = [x == I.xm + up - um, up >= 0, um >= 0, x >= 0, x <= I.cap]
    if fixA:
        cons.append(x[:I.N] == I.xm[:I.N])
    cons.append(cp.sum(up - um) + I.kp @ up + I.km @ um <= I.h)
    obj = I.mu @ x - 0.5 * GAMMA * cp.quad_form(x, cp.psd_wrap(I.Sig)) - (I.kp @ up + I.km @ um)
    p = cp.Problem(cp.Maximize(SCALE * obj), cons); p.solve(solver=solver, **opts(solver))
    eta = max(0.0, float(cons[-1].dual_value) / SCALE) if cons[-1].dual_value is not None else 0.0
    return x.value, eta, p.status


def mk(a1, xm1, kp1, km1, kE=0.0, cE=0.0, lam=LAM, h=1.0, xEm=None, others=True):
    alpha = np.array([a1, GAMMA * V * 0.1, GAMMA * V * 0.1])       # funds 2, 3 at their band centres
    return Inst(BA, BE, alpha, V, [kp1, 0.002, 0.002], [km1, 0.002, 0.002], [xm1, 0.1, 0.1], 0.25, lam=np.asarray(lam, float),
                cE=cE, kEp=kE, kEm=kE, h=h, xEm=xEm)


def interior(I, x):
    return bool(np.all(x[I.N:] > INTERIOR) and np.all(x[I.N:] < I.cap[I.N:] - INTERIOR))


def slope_set(I, x, i):
    u = x[i] - I.xm[i]
    if u > TRADE:
        return [I.kp[i]]
    if u < -TRADE:
        return [-I.km[i]]
    return [-I.km[i], I.kp[i]]


def part1_ok(I, x, eta, tol=1e-7):
    """Part 1's multiplier criterion at x with eta (one-sided at the bounds)."""
    g = I.g(x); ok = True
    for i in range(I.n):
        ts = slope_set(I, x, i)
        R = [g[i] - eta - (1 + eta) * t for t in ts]
        lo, hi = min(R), max(R)
        at0, atc = x[i] <= TRADE, x[i] >= I.cap[i] - TRADE
        if at0 and not atc:
            ok &= lo <= tol
        elif atc and not at0:
            ok &= hi >= -tol
        elif not at0:
            ok &= lo <= tol and hi >= -tol
    return bool(ok)


def part2_test(I):
    """Part 2: at the ETF-only optimum x_E, is there eta in I with every fund held? Returns (verdict, I interval)."""
    xE, etaE, _ = solve(I, fixA=True)
    g = I.g(xE)
    lo, hi = 0.0, (0.0 if I.cash(xE) > 1e-9 else np.inf)
    for j in range(I.N, I.n):                                       # ETF conditions -> interval of eta
        at0, atc = xE[j] <= TRADE, xE[j] >= I.cap[j] - TRADE
        for t in slope_set(I, xE, j):
            pass
        u = xE[j] - I.xm[j]
        # R_j(eta) = g_j - eta - (1 + eta) t = (g_j - t) - eta (1 + t), t in T_j
        if u > TRADE or u < -TRADE:
            t = I.kp[j] if u > 0 else -I.km[j]
            e0 = (g[j] - t) / (1 + t)
            if not (at0 or atc):
                lo, hi = max(lo, e0 - 1e-9), min(hi, e0 + 1e-9)
            elif at0:
                lo = max(lo, e0 - 1e-9)
            else:
                hi = min(hi, e0 + 1e-9)
        else:
            e_hi = (g[j] + I.km[j]) / (1 - I.km[j])                 # R with t = -km: eta <= e_hi keeps R >= 0 possible
            e_lo = (g[j] - I.kp[j]) / (1 + I.kp[j])                 # R with t = kp: eta >= e_lo keeps R <= 0 possible
            if not at0:
                hi = min(hi, e_hi + 1e-9)
            if not atc:
                lo = max(lo, e_lo - 1e-9)
    if lo > hi:
        return None, (lo, hi)
    # funds held at x_E for some eta in [lo, hi]: g_i in [eta - (1+eta) km, eta + (1+eta) kp] (one-sided at bounds)
    flo, fhi = lo, hi
    for i in range(I.N):
        at0, atc = I.xm[i] <= TRADE, I.xm[i] >= I.cap[i] - TRADE
        # g_i <= eta + (1 + eta) kp  <=>  eta >= (g_i - kp)/(1 + kp)
        if not atc:
            flo = max(flo, (g[i] - I.kp[i]) / (1 + I.kp[i]) - 1e-9)
        # g_i >= eta - (1 + eta) km  <=>  eta <= (g_i + km)/(1 - km)
        if not at0:
            fhi = min(fhi, (g[i] + I.km[i]) / (1 - I.km[i]) + 1e-9)
    return bool(flo <= fhi), (lo, hi)


# ---------------------------------------------------------------- curve 1: part 3 ----------
def c1(args):
    rates, xm1, lam, PLs = args
    I = mk(0.0, xm1, *rates, lam=lam)
    if PLs != 1.0:
        I.St = SF + PL * PLs; I.bTB = np.linalg.solve(GAMMA * I.St, I.lam)
        I.mu = np.concatenate([I.alpha + I.BA @ I.lam, I.BE @ I.lam - I.cE]); I.Sig = I.B @ I.St @ I.B.T + I.Dres
    out = []
    for a in np.round(np.linspace(-0.01, 0.01, 81), 6):
        I.alpha[0] = a; I.mu = np.concatenate([I.alpha + I.BA @ I.lam, I.BE @ I.lam - I.cE])
        x, eta, st = solve(I); xo, _, st2 = solve(I, "OSQP")
        m = a - GAMMA * V * xm1
        tr = x[0] - xm1
        dec = "buy" if tr > TRADE else ("sell" if tr < -TRADE else "hold")
        pred = "buy" if m > rates[0] else ("sell" if m < -rates[1] else "hold")
        clip = float(np.clip(np.clip(xm1, (a - rates[0]) / (GAMMA * V), (a + rates[1]) / (GAMMA * V)), 0, 0.25))
        y = np.linalg.solve(GAMMA * I.St, I.lam)
        xE_f = np.linalg.solve(BE.T, y - BA.T @ x[:3])
        out.append(dict(a=float(a), dec=dec, pred=pred, edge=bool(min(abs(m - rates[0]), abs(m + rates[1])) < 1e-7),
                        hyp=interior(I, x) and I.cash(x) > INTERIOR, x1=float(x[0]), clip=clip, etf_err=float(np.abs(x[3:] - xE_f).max()),
                        dx=float(np.abs(x - xo).max()), p1=part1_ok(I, x, eta), status=[st, st2]))
    return dict(rates=rates, xm1=xm1, lam=list(lam), PLs=PLs, rows=out)


# ---------------------------------------------------------------- thresholds by root-finding ----------
def onset(make, side, lo=-0.05, hi=0.05):
    """alpha_hat_1 at which fund 1's purchase (side +1) or sale (side -1) starts: roots at trades 1e-4 and 2e-4,
    extrapolated linearly to 0 (Deviation 2). Returns (alpha, eta there, instance at onset+)."""
    def tr(a, tau):
        I = make(a); x, _, _ = solve(I); return side * (x[0] - I.xm[0]) - tau
    try:
        a1 = brentq(lambda a: tr(a, 1e-4), lo, hi, xtol=1e-12)
        a2 = brentq(lambda a: tr(a, 2e-4), lo, hi, xtol=1e-12)
    except ValueError:
        return None, None, None
    a0 = a1 - (a2 - a1)
    I = make(a1); x, eta, _ = solve(I)
    return a0, eta, (I, x)


def c2(args):
    rE, fee, xm1, l1 = args
    kp = km = 0.002
    xAm = np.array([xm1, 0.1, 0.1])                                 # ETF incumbents fixed at the base premium's remainder
    xEm = np.clip(np.linalg.solve(BE.T, np.linalg.solve(GAMMA * (SF + PL), LAM) - BA.T @ xAm), 0, 1)
    make = lambda a: mk(a, xm1, kp, km, kE=rE, cE=fee, lam=[l1, LAM[1]], xEm=xEm)
    a0, eta, (I, x) = onset(make, +1)
    if a0 is None:
        return dict(rE=rE, fee=fee, xm1=xm1, l1=l1, ok=False)
    r = BA[0] @ np.linalg.inv(BE)                              # r_1 = R' (B^A_1)'
    hp = float(np.sum(np.maximum(r, 0) * rE + np.maximum(-r, 0) * rE)); hm = hp
    A = a0 + r @ np.full(2, fee) - GAMMA * V * xm1
    I0 = make(a0 - 1e-4); x0, _, _ = solve(I0)
    dE = x[3:] - x0[3:]
    rehedge = bool(np.all(np.sign(dE[np.abs(r) > 0]) == -np.sign(r[np.abs(r) > 0])) and np.all(np.abs(dE[np.abs(r) > 0]) > 1e-7))
    opposite = bool(np.all(np.sign(dE[np.abs(r) > 0]) == np.sign(r[np.abs(r) > 0])) and np.all(np.abs(dE[np.abs(r) > 0]) > 1e-7))
    tE = x[3:] - I.xm[3:]
    exp_pos = float(np.sum(np.abs(r) * (tE < -1e-7)) / np.sum(np.abs(r))) if np.all(np.abs(tE) > 1e-7) else None
    return dict(rE=rE, fee=fee, xm1=xm1, l1=l1, ok=True, A=float(A), etf_trade=[float(v) for v in tE], exp_pos=exp_pos, lo=kp - hm, hi=kp + hp, pos=float((A - (kp - hm)) / (hp + hm)) if hp + hm > 0 else None,
                rehedge=rehedge, opposite=opposite, hyp=interior(I, x) and interior(I0, x0) and I.cash(x) > INTERIOR, eta=eta)


def c2_suff(idx):
    rng = np.random.default_rng([2034, 0, idx])
    alpha = rng.uniform(-0.01, 0.01, 3); kp, km = rng.uniform(0, 0.01, 3), rng.uniform(0, 0.01, 3)
    xm = rng.uniform(0, 0.25, 3); kE = rng.uniform(0, 0.005); fee = rng.uniform(0, 0.001)
    I = Inst(BA, BE, alpha, V, kp, km, xm, 0.25, cE=fee, kEp=kE, kEm=kE)
    x, eta, st = solve(I)
    R = np.linalg.inv(BE); out = []
    for i in range(3):
        r = R.T @ BA[i]; hp = hm = float(np.sum(np.abs(r)) * kE)
        A0 = alpha[i] + r @ np.full(2, fee) - GAMMA * V * xm[i]
        tr = x[i] - xm[i]
        if A0 > kp[i] + hp and xm[i] < 0.25:
            out.append(("buy", bool(tr > TRADE)))
        if A0 < -km[i] - hm and xm[i] > 0:
            out.append(("sell", bool(tr < -TRADE)))
    return dict(idx=idx, hyp=interior(I, x) and I.cash(x) > INTERIOR and eta < 1e-9, cases=out)


# ---------------------------------------------------------------- curve 3: binding budget ----------
def c3(args):
    name, h, rE = args
    a_named, kf, _ = NAMED[name]
    make = lambda a: mk(a, 0.1, kf, kf, kE=rE, h=h, xEm=np.zeros(2))
    out = dict(name=name, h=h, rE=rE)
    r = BA[0]; sr = float(r.sum())
    for side in (+1, -1):
        a0, eta, pack = onset(make, side)
        if a0 is None:
            out[f"side{side}"] = None; continue
        I, x = pack
        m = a0 - GAMMA * V * 0.1
        hp = hm = float(np.sum(np.abs(r)) * rE)
        if side > 0:
            literal = eta + (1 + eta) * kf; corrected = eta * (1 - sr) + (1 + eta) * kf
            br = ((1 + eta) * (kf - hm), (1 + eta) * (kf + hp))
        else:
            literal = eta - (1 + eta) * kf; corrected = eta * (1 - sr) - (1 + eta) * kf
            br = (-(1 + eta) * (kf + hm), -(1 + eta) * (kf - hp))
        out[f"side{side}"] = dict(m=float(m), eta=eta, literal=literal, corrected=corrected, A_adj=float(m - eta * (1 - sr)), br=br,
                                  hyp=interior(I, x), cash=I.cash(x))
    return out


# ---------------------------------------------------------------- curve 4: parts 1-2 on random draws ----------
def c4(idx):
    rng = np.random.default_rng([2034, 1, idx])
    alpha = rng.uniform(-0.01, 0.01, 3); kp, km = rng.uniform(0, 0.01, 3), rng.uniform(0, 0.01, 3)
    xm = rng.uniform(0, 0.25, 3); kE = rng.uniform(0, 0.005); fee = rng.uniform(0, 0.001)
    lam = rng.uniform(-0.01, 0.04, 2); h = rng.choice([1.0, 0.3, 0.05]); xEm = rng.uniform(0, 0.8, 2)
    I = Inst(BA, BE, alpha, V, kp, km, xm, 0.25, lam=lam, cE=fee, kEp=kE, kEm=kE, h=h, xEm=xEm)
    x, eta, st = solve(I)
    traded = bool(np.any(np.abs(x[:3] - xm) > TRADE))
    verdict, Iv = part2_test(I)
    etf_bound = bool(np.any(x[3:] <= TRADE) or np.any(x[3:] >= 1 - TRADE))
    return dict(idx=idx, p1=part1_ok(I, x, eta), traded=traded, part2=verdict, eta=eta, etf_bound=etf_bound, status=st)


# ---------------------------------------------------------------- curve 5: part 6, exact DP ----------
def _interp_rows(V, mg, mq):
    """Rows of V (indexed by the m grid) linearly interpolated at the points mq (clamped at the ends)."""
    q = np.clip(mq, mg[0], mg[-1]); step = mg[1] - mg[0]
    i0 = np.minimum(((q - mg[0]) / step).astype(int), len(mg) - 2); f = (q - mg[i0]) / step
    return V[i0] * (1 - f)[:, None] + V[i0 + 1] * f[:, None]


def c5(args):
    """Part 6: one instrument, pure-learning marking; V_t(x, m) = max_y [m y - (c_t/2) y^2 - C(y - x) + beta E V_{t+1}(y, m')]."""
    beta, T, kap, pr, hfac = args
    s2 = 0.02 ** 2; p0 = pr * s2
    p = [1 / (1 / p0 + t / s2) for t in range(T + 1)]
    c = [GAMMA * (s2 + p[t]) for t in range(T)]
    w1 = 2 * kap / c[0]
    hx = w1 / (200 * hfac)
    sd = np.sqrt(p0 - p[T])
    mg = np.linspace(-4 * sd - 3 * kap, 4 * sd + 3 * kap, 401 * hfac)
    xg = np.arange(0, (mg.max() + kap) / min(c) + w1 + hx, hx)
    gh_x, gh_w = np.polynomial.hermite_e.hermegauss(20); gh_w = gh_w / gh_w.sum()
    Vn = np.zeros((len(mg), len(xg))); res = []
    for t in range(T - 1, -1, -1):
        s_inn = np.sqrt(max(p[t] - p[t + 1], 0.0))
        cont = np.zeros_like(Vn)
        if t < T - 1:
            for z, wz in zip(gh_x, gh_w):
                cont += wz * _interp_rows(Vn, mg, mg + s_inn * z)
        def W_at(m):
            row = _interp_rows(cont, mg, np.array([m]))[0] if t < T - 1 else np.zeros(len(xg))
            return m * xg - 0.5 * c[t] * xg ** 2 + beta * row
        def buys_from_zero(m):
            Wm = W_at(m); return float(np.max(Wm[1:] - kap * xg[1:])) > Wm[0] + 1e-15
        lo_m, hi_m = -3 * kap, 3 * kap
        thr = None
        if not buys_from_zero(lo_m) and buys_from_zero(hi_m):
            for _ in range(50):
                mid = 0.5 * (lo_m + hi_m)
                lo_m, hi_m = (lo_m, mid) if buys_from_zero(mid) else (mid, hi_m)
            thr = 0.5 * (lo_m + hi_m)
        W = mg[:, None] * xg[None, :] - 0.5 * c[t] * xg[None, :] ** 2 + beta * cont
        U, A = fastdp.l1(W, kap * hx, kap * hx, axis=1)
        Vn = U
        idx = np.arange(len(xg)); band = np.full((len(mg), 2), np.nan)
        for k in range(len(mg)):
            nt = np.where(A[k] == idx)[0]
            if nt.size:
                band[k] = (xg[nt.min()], xg[nt.max()])
        one_lo, one_hi = (mg - kap) / c[t], (mg + kap) / c[t]
        inner = (band[:, 0] > hx) & (one_lo > hx) & (band[:, 1] < xg[-1] - w1) & (np.abs(mg) <= max(2 * sd, 3 * kap))   # Deviation 3: off the clamped m-grid edges
        exc = float(np.max(np.concatenate([one_lo[inner] - band[inner, 0], band[inner, 1] - one_hi[inner]]))) if inner.any() else None
        eq = float(np.max(np.abs(np.concatenate([band[inner, 0] - one_lo[inner], band[inner, 1] - one_hi[inner]])))) if inner.any() else None
        res.append(dict(t=t, thr=thr, lo=(1 - beta) * kap, hi=kap + beta * kap, excess=exc, eq=eq, hx=hx, c=c[t],
                        width_ratio=float(np.median((band[inner, 1] - band[inner, 0]) / (one_hi[inner] - one_lo[inner]))) if inner.any() else None))
    return dict(beta=beta, T=T, kap=kap, pr=pr, hfac=hfac, rows=res[::-1])


def main():
    t0 = time.time(); S = {}
    lams = [tuple(LAM), (0.0, 0.0), (0.03, 0.01), (0.01, 0.03), (0.02, -0.005)]
    with mp.Pool(9) as pool:
        a1 = [(r, float(x), tuple(LAM), 1.0) for r in ((0.002, 0.002), (0.005, 0.001), (0.0, 0.0)) for x in np.round(np.linspace(0, 0.25, 26), 6)]
        a1 += [(r, float(x), l, s) for r in ((0.002, 0.002), (0.005, 0.001)) for x in (0.0, 0.1, 0.25) for l in lams for s in (0.25, 1.0, 4.0)]
        S["c1"] = pool.map(c1, a1); print("c1", time.time() - t0, flush=True)
        S["c2"] = pool.map(c2, [(rE, fee, xm, l1) for rE in (0, 0.0005, 0.001, 0.0025, 0.005, 0.01) for fee in (0, 0.0005, 0.001)
                                for xm in (0.0, 0.1) for l1 in (0.005, 0.015, 0.03)]); print("c2", time.time() - t0, flush=True)
        S["c2_suff"] = pool.map(c2_suff, range(500)); print("c2s", time.time() - t0, flush=True)
        S["c3"] = pool.map(c3, [(nm, h, rE) for nm in NAMED for h in (1.2, 1.0, 0.8, 0.6, 0.4, 0.3, 0.2, 0.1) for rE in (0.0, 0.0025)]); print("c3", time.time() - t0, flush=True)
        S["c4"] = pool.map(c4, range(300)); print("c4", time.time() - t0, flush=True)
        S["c5"] = pool.map(c5, [(b, T, k, pr, 1) for b in (0.9, 0.95, 0.99, 1.0) for T in (2, 4, 8, 20) for k in (0.001, 0.005) for pr in (0.03, 0.3)]
                           + [(1.0, 8, 0.001, 0.3, 2), (0.95, 20, 0.005, 0.03, 2)]); print("c5", time.time() - t0, flush=True)
    S["seconds"] = time.time() - t0
    json.dump(S, open(HERE / "summary.json", "w"), separators=(",", ":"), default=lambda o: o.tolist() if hasattr(o, "tolist") else (None if o != o else str(o)))
    print("done", S["seconds"])


if __name__ == "__main__":
    main()
