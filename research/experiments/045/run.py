"""Experiment 045: claims 110 (one ETF, two scalars; mathb/claim110-one-etf-two-scalars aaefdb4a) and 111 (the
incumbent-aware first stage; mathb/claim111-incumbent-aware-stage 7c9565cd) against exact joint solvers.
Registered design: experiments/045-claims110-111-check.md.  Run: uv run python experiments/045/run.py
"""
import importlib.util
import json
import multiprocessing as mp
import time
from pathlib import Path

import cvxpy as cp
import numpy as np

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("run044", HERE.parent / "044" / "run.py")
m44 = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(m44)
GAMMA, SCALE, OPT = m44.GAMMA, m44.SCALE, m44.OPT


# ------------------------------------------------------------------ claim 110
class One:
    def __init__(s, **k):
        s.__dict__.update(k)

    def clip(s, m, eta):
        lo = (s.at + s.r * m - eta - (1 + eta) * s.kp) / (GAMMA * s.v)
        hi = (s.at + s.r * m - eta + (1 + eta) * s.km) / (GAMMA * s.v)
        return np.clip(np.minimum(np.maximum(s.xm, lo), hi), 0, s.cap)

    def p(s, m, eta):
        return (s.mu - m) / (GAMMA * s.sEE) - s.r @ s.clip(m, eta)

    def root(s, f, target, lo=-2.0, hi=2.0):
        """Root of a decreasing function f(m) = target, by bisection."""
        for _ in range(200):
            mid = 0.5 * (lo + hi)
            if f(mid) > target:
                lo = mid
            else:
                hi = mid
        return 0.5 * (lo + hi)

    def at_eta(s, eta):
        """Part 2 (and part 5) at a fixed eta: the status, m*, p* and the funds."""
        tb, ts = eta + (1 + eta) * s.kEp, eta - (1 + eta) * s.kEm
        pf = lambda m: s.p(m, eta)
        m0 = s.root(pf, 0.0)
        if s.sE > 0:
            traded = lambda th: s.root(lambda m: -(m - GAMMA * s.sE * s.p(m, eta)), -th)     # m - gamma sE p(m) = th (increasing)
        else:
            traded = lambda th: th
        if s.pm > 0:
            mI = s.root(pf, s.pm); eff = mI - GAMMA * s.sE * s.pm
            if eff > tb:
                st, m = "B", traded(tb)
            elif eff >= ts:
                st, m = "I", mI
            else:
                m1 = traded(ts)
                st, m = ("S", m1) if s.p(m1, eta) > 0 and m0 > ts else ("Z", m0)
        else:
            mI = None
            if m0 <= tb:
                st, m = "Z", m0
            else:
                st, m = "B", traded(tb)
        x = s.clip(m, eta)
        p = {"Z": 0.0, "I": s.pm}.get(st, s.p(m, eta))
        return dict(st=st, m=m, m0=m0, mI=mI, x=x, p=max(p, 0.0))

    def cost(s, x, p):
        u, e = x - s.xm, p - s.pm
        return float(s.kp @ np.maximum(u, 0) + s.km @ np.maximum(-u, 0) + s.kEp * max(e, 0) + s.kEm * max(-e, 0))

    def k(s, x, p):
        return float(s.h - np.sum(x - s.xm) - (p - s.pm) - s.cost(x, p))

    def reduce(s):
        a0 = s.at_eta(0.0)
        if s.k(a0["x"], a0["p"]) >= 0:
            return a0, 0.0
        lo, hi = 0.0, 1.0
        while s.k(*(lambda a: (a["x"], a["p"]))(s.at_eta(hi))) < 0:
            hi *= 2
        for _ in range(100):
            mid = 0.5 * (lo + hi); a = s.at_eta(mid)
            if s.k(a["x"], a["p"]) < 0:
                lo = mid
            else:
                hi = mid
        return s.at_eta(hi), hi

    def joint(s, solver="CLARABEL"):
        N = len(s.r); x, p = cp.Variable(N), cp.Variable(nonneg=True)
        ap, am, ep, em = cp.Variable(N, nonneg=True), cp.Variable(N, nonneg=True), cp.Variable(nonneg=True), cp.Variable(nonneg=True)
        C = s.kp @ ap + s.km @ am + s.kEp * ep + s.kEm * em; w = p + s.r @ x
        bud = (s.h - cp.sum(x - s.xm) - (p - s.pm) - C >= 0) if s.h is not None else None
        obj = s.at @ x - 0.5 * GAMMA * cp.sum(cp.multiply(s.v, cp.square(x))) + s.mu * w - 0.5 * GAMMA * s.sEE * cp.square(w) - 0.5 * GAMMA * s.sE * cp.square(p) - C
        pr = cp.Problem(cp.Maximize(SCALE * obj), [x - s.xm == ap - am, p - s.pm == ep - em, x >= 0, x <= s.cap] + ([bud] if bud is not None else []))
        if solver == "CLARABEL":
            pr.solve(solver="CLARABEL", **OPT)
        else:
            pr.solve(solver="OSQP", eps_abs=1e-10, eps_rel=1e-10, max_iter=400000, polish=True)
        return np.array(x.value), float(max(p.value, 0.0)), (float(bud.dual_value) / SCALE if bud is not None else 0.0)


def gen110(idx):
    rng = np.random.default_rng([2045, 0, idx])
    N = (1, 3, 6)[idx % 3]
    bA = rng.uniform(0.3, 1.5, N) * np.where(np.arange(N) % 3 == 2, -1.0, 1.0)
    lam, sf, cE = rng.uniform(-0.01, 0.03), rng.uniform(0.001, 0.01), rng.uniform(0, 0.002)
    ah = rng.uniform(-0.01, 0.01, N); v = 0.02 ** 2 * (1 + rng.uniform(0.01, 3, N))
    kp, km = rng.uniform(0, 0.02, N), rng.uniform(0, 0.02, N)
    cap = rng.choice([0.25, 1.0], N); xm = rng.uniform(0, 1, N) * cap
    kEp, kEm = rng.uniform(0, 0.005, 2); pm = 0.0 if rng.random() < 0.5 else rng.uniform(0, 0.5)
    hfac = rng.uniform(0.3, 1.5)
    sE = rng.uniform(0.005 ** 2, 0.02 ** 2) if idx >= 500 else 0.0
    sf2 = 0.08 ** 2 + sf ** 2                         # experiment 040's factor variance plus the premium's
    s = One(r=bA, mu=lam - cE, sEE=sf2, at=ah + bA * cE, v=v, kp=kp, km=km, cap=cap, xm=xm, kEp=kEp, kEm=kEm, pm=pm, sE=sE, h=None)
    x, p, _ = s.joint(); need = float(np.sum(x - xm) + (p - pm) + s.cost(x, p))
    s.h = max(need * hfac, 1e-3)
    return s


def run110(idx):
    s = gen110(idx)
    xJ, pJ, etaJ = s.joint(); xO, pO, _ = s.joint("OSQP")
    red, eta = s.reduce()
    wJ = pJ + s.r @ xJ; mJ = s.mu - GAMMA * s.sEE * wJ
    stJ = "Z" if pJ <= 1e-7 else ("B" if pJ > s.pm + 1e-7 else ("S" if pJ < s.pm - 1e-7 else "I"))
    kJ = s.k(xJ, pJ)
    # part 3 monotonicity and part 1's q monotone in m
    etas = np.linspace(0, 2 * eta + 0.01, 50); ks = [s.k(a["x"], a["p"]) for a in map(s.at_eta, etas)]
    ms = np.linspace(red["m"] - 0.02, red["m"] + 0.02, 50); qs = [s.r @ s.clip(m, eta) for m in ms]
    # part 4(a): direction from the incumbent at the optimum's prices
    g0 = s.at + s.r * red["m"] - GAMMA * s.v * s.xm
    pred = np.where((g0 > eta + (1 + eta) * s.kp + 1e-12) & (s.xm < s.cap), 1, np.where((g0 < eta - (1 + eta) * s.km - 1e-12) & (s.xm > 0), -1, 0))
    obs = np.where(xJ > s.xm + 1e-7, 1, np.where(xJ < s.xm - 1e-7, -1, 0))
    tb, ts = eta + (1 + eta) * s.kEp, eta - (1 + eta) * s.kEm
    near = min([abs(red["m0"] - tb), abs(red["m0"] - ts)] + ([abs(red["mI"] - tb), abs(red["mI"] - ts)] if red["mI"] is not None else []))
    return dict(idx=idx, N=len(s.r), sE=s.sE, dx=float(max(np.max(np.abs(red["x"] - xJ)), abs(red["p"] - pJ))), st=red["st"], stJ=stJ, m=red["m"], mJ=float(mJ),
                eta=eta, etaJ=etaJ, binding=bool(kJ < 1e-7 and etaJ > 1e-7), solver_dx=float(max(np.max(np.abs(xO - xJ)), abs(pO - pJ))),
                k_mono=bool(np.all(np.diff(ks) >= -1e-12)), q_mono=bool(np.all(np.diff(qs) >= -1e-15)),
                dir_ok=bool(np.all(pred == obs)), near_edge=float(near), pm=s.pm)


# ------------------------------------------------------------------ claim 111
def run111(args):
    kind, idx = args
    I = m44.gen(kind, idx)
    J1 = I.solve(); xA, xE = J1["xA"], J1["xE"]; J = I.Qv(xA, xE); wJ = xE + I.Q @ xA
    Sinv = np.linalg.inv(I.S); out = dict(kind=kind, idx=idx)
    X1 = I.solve(fundsfixed=True); x1A, x1E = X1["xA"], X1["xE"]; w1 = x1E + I.Q @ x1A; eta1 = max(X1["eta"], 0.0)
    st1 = m44.statuses(I, x1E); k1 = I.k(x1A, x1E)
    for name, w in (("aware", w1), ("041", I.stage1())):
        F = I.solve("fibre", wfix=w)
        if F is None:
            out[name] = None; continue
        x2A, x2E = F["xA"], F["xE"]; Lam = J - I.Qv(x2A, x2E); s_dual = F["s"]; eta2 = max(F["eta"], 0.0); k2 = I.k(x2A, x2E)
        st2 = m44.statuses(I, x2E)
        gE = I.mu - GAMMA * I.S @ w
        # the residual from its definition, at ETFs traded to an interior holding (unique multipliers there when the budget is slack)
        mv = m44.etf_moves(I, x2E)
        s_def = {j: gE[j] - eta2 - (1 + eta2) * (I.kEp[j] if mv[j] == "bought_interior" else -I.kEm[j]) for j in range(2) if mv[j] in ("bought_interior", "sold_interior")}
        exact = bool(max(np.max(np.abs(x2A - xA)), np.max(np.abs(x2E - xE))) <= 1e-5)
        dA, dw = xA - x2A, wJ - w
        rec = dict(exact=exact, Lam=Lam, s_dual=s_dual.tolist(), s_def=s_def, eta2=eta2, k2=k2, moves=mv, st2="".join(st2),
                   lower=float(0.5 * GAMMA * (dA @ (I.v * dA) + dw @ I.S @ dw)), up1=float(s_dual @ dw), up2=float(s_dual @ Sinv @ s_dual / (2 * GAMMA)),
                   up1_neg=float(-s_dual @ dw), up2_neg=float(s_dual @ Sinv @ s_dual / (2 * GAMMA)),
                   wgap=float(np.sqrt(dw @ I.S @ dw)), snorm=float(np.sqrt(s_dual @ Sinv @ s_dual) / GAMMA))
        if name == "aware":
            g1 = I.at - GAMMA * I.v * x1A + I.Q.T @ (I.mu - GAMMA * I.S @ w1)
            held = all((g1[i] <= eta1 + (1 + eta1) * I.kp[i] + 1e-9 or I.xm[i] >= I.cap[i] - 1e-12) and (g1[i] >= eta1 - (1 + eta1) * I.km[i] - 1e-9 or I.xm[i] <= 1e-12) for i in range(I.N))
            T1 = [j for j in range(2) if st1[j] in "BS"]; F1 = [j for j in range(2) if st1[j] in "ZI"]
            kept = all(st2[j] == st1[j] for j in range(2)) and all(x2E[j] > 1e-7 for j in T1)
            slack = bool(k1 > 1e-9 and eta1 <= 1e-9 and k2 > 1e-9 and eta2 <= 1e-9)     # Deviation 2: slack also by the multiplier
            c3b = bool(not F1 and slack and kept)
            c3c = bool(F1 and slack and kept)
            rec.update(held=bool(held), x1_is_J=bool(max(np.max(np.abs(x1A - xA)), np.max(np.abs(x1E - xE))) <= 1e-5), c3b=c3b, c3c=c3c, st1="".join(st1), k1=k1, eta1=eta1)
            if c3c:
                QF = I.Q[F1, :] @ (x2A - I.xm)
                gline = I.at - GAMMA * I.v * x2A + I.Q.T @ (I.mu - GAMMA * I.S @ w1)
                rec.update(sT=float(max([abs(s_dual[j]) for j in T1] + [0.0])), QF=float(np.max(np.abs(QF))), lines3c=bool(m44.fund_line(I, gline, x2A, 0.0) <= 1e-7))
        out[name] = rec
    return out


def main():
    t0 = time.time()
    with mp.Pool(8) as pool:
        r110 = pool.map(run110, range(600), chunksize=4); print("110", time.time() - t0, flush=True)
        r111 = pool.map(run111, [("multi", i) for i in range(500)] + [("one", i) for i in range(500)], chunksize=4)
    S = dict(c110=r110, c111=r111, seconds=time.time() - t0,
             statement="claim 110 at aaefdb4a, claim 111 at 7c9565cd (mathb's branches, proposed)")
    json.dump(S, open(HERE / "summary.json", "w"), separators=(",", ":"), default=lambda o: o.tolist() if hasattr(o, "tolist") else (int(o) if isinstance(o, np.integer) else float(o)))
    print("done", S["seconds"])


if __name__ == "__main__":
    main()
