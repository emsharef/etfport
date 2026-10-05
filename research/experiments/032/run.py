"""Experiment 032: claim 106 (the ETF-only restriction's cost, one review, M7) against an independent one-review solver.
Registered design: experiments/032-etf-only-cost-check.md.  Run: uv run python experiments/032/run.py

Experiment 029's formulation (`Inst`, bp-scaled objectives, CLARABEL and OSQP) with the three action classes imposed
on the fund block: F (none), E^- (x^A <= x^{A-}), E^0 (x^A = x^{A-}). Formula side coded from claim 106's Statement.
"""
import importlib.util
import itertools
import json
import multiprocessing as mp
import time
from pathlib import Path

import cvxpy as cp
import numpy as np

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("run029", HERE.parent / "029" / "run.py")
m29 = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(m29)
Inst, GAMMA, SF, PL, LAM, V, SCALE, INTERIOR = m29.Inst, m29.GAMMA, m29.SF, m29.PL, m29.LAM, m29.V, m29.SCALE, m29.INTERIOR
BA = m29.BA3
BE_SPAN = np.eye(2)                         # Deviation 1 (experiment 029's Deviation 1)
BA_UNR = np.array([[1.0, 0.5], [1.0, 0.0], [1.0, 0.0]])
BE_UNR = np.array([[1.0, 0.0]])
RATE = 0.002
TRADE = 1e-5
NAMED = {"equity-style": (-0.0019, 0.005), "fixed-income-style": (0.0020, 0.002)}


def opts(solver):
    return dict(CLARABEL=dict(tol_gap_abs=1e-12, tol_gap_rel=1e-10, tol_feas=1e-10, max_iter=500),
                OSQP=dict(eps_abs=1e-10, eps_rel=1e-10, polish=True, max_iter=400000))[solver]


def solve(I, cls, solver):
    n = I.n; x, up, um = cp.Variable(n), cp.Variable(n), cp.Variable(n)
    cons = [x == I.xm + up - um, up >= 0, um >= 0, x >= 0, x <= I.cap]
    if cls == "E-":
        cons.append(x[:I.N] <= I.xm[:I.N])
    elif cls == "E0":
        cons.append(x[:I.N] == I.xm[:I.N])
    cons.append(cp.sum(up - um) + I.kp @ up + I.km @ um <= I.h)
    obj = I.mu @ x - 0.5 * GAMMA * cp.quad_form(x, cp.psd_wrap(I.Sig)) - (I.kp @ up + I.km @ um)
    p = cp.Problem(cp.Maximize(SCALE * obj), cons); p.solve(solver=solver, **opts(solver))
    return x.value, I.Q(x.value), p.status


def classes(I):
    out = {}
    for s in ("CLARABEL", "OSQP"):
        out[s] = {c: solve(I, c, s) for c in ("F", "E-", "E0")}
    a, b = out["CLARABEL"], out["OSQP"]
    dis = max(abs(a[c][1] - b[c][1]) for c in a)
    hyp = all(np.all(a[c][0][I.N:] > INTERIOR) and np.all(a[c][0][I.N:] < I.cap[I.N:] - INTERIOR) and I.cash(a[c][0]) > INTERIOR for c in a)
    J, Jm, J0 = a["F"][1], a["E-"][1], a["E0"][1]
    xJ = a["F"][0][:I.N]
    return dict(Cm=J - Jm, sale=Jm - J0, C0=J - J0, dis=dis, hyp=bool(hyp),
                bought=bool(np.any(xJ > I.xm[:I.N] + TRADE)), traded=bool(np.any(np.abs(xJ - I.xm[:I.N]) > TRADE)),
                status=[a[c][2] for c in a] + [b[c][2] for c in b], x1=float(xJ[0]))


# ---------------------------------------------------------------- formula side (claim 106) ----------
def psi(a, al, v, kp, km, xm):
    return al * a - 0.5 * GAMMA * v * a ** 2 - kp * max(a - xm, 0) - km * max(xm - a, 0)


def part2(al, v, kp, km, xm, cap):
    """Per-fund terms of C^- and J^- - J^0 (part 2), with the cap and floor forms."""
    p = al - kp - GAMMA * v * xm; s = GAMMA * v * xm - al - km
    lo, hi = (al - kp) / (GAMMA * v), (al + km) / (GAMMA * v)
    c = 0.0
    if p > 0:
        c = p ** 2 / (2 * GAMMA * v) if lo <= cap else psi(cap, al, v, kp, km, xm) - psi(xm, al, v, kp, km, xm)
    e = 0.0
    if s > 0:
        e = s ** 2 / (2 * GAMMA * v) if hi >= 0 else psi(0.0, al, v, kp, km, xm) - psi(xm, al, v, kp, km, xm)
    return c, e


def gfun(m, d, v):
    if m <= 0:
        return 0.0
    return m ** 2 / (2 * GAMMA * v) if m <= GAMMA * v * d else m * d - 0.5 * GAMMA * v * d ** 2


def formula(I, reduced_fund=None):
    """Part 2 (or part 3 with reduced moments for fund 0) summed over funds."""
    C = E = 0.0
    for i in range(I.N):
        al, v = I.alpha[i], I.v[i]
        if reduced_fund is not None and i == 0:
            al, v = reduced_fund
        c, e = part2(al, v, I.kp[i], I.km[i], I.xm[i], I.cap[i]); C += c; E += e
    return C, E


def bracket(I, kE):
    """Part 4's brackets: re-hedge costs h^+-, reduced marginal A^0 (Sigma_E = 0)."""
    R = np.linalg.inv(I.BE)
    Cl = Cu = El = Eu = 0.0
    for i in range(I.N):
        r = R.T @ I.BA[i]
        hp = float(np.sum(np.maximum(r, 0) * kE + np.maximum(-r, 0) * kE)); hm = hp      # symmetric ETF rates
        A0 = I.alpha[i] + r @ I.cE - GAMMA * I.v[i] * I.xm[i]
        dB, dS = I.cap[i] - I.xm[i], I.xm[i]
        Cl += gfun(A0 - I.kp[i] - hp, dB, I.v[i]); Cu += gfun(A0 - I.kp[i] + hm, dB, I.v[i])
        El += gfun(-A0 - I.km[i] - hm, dS, I.v[i]); Eu += gfun(-A0 - I.km[i] + hp, dS, I.v[i])
    return Cl, Cu, El, Eu


def reduced(I, i=0):
    Q_, _ = np.linalg.qr(I.BE.T); PiR = Q_ @ Q_.T; PiU = np.eye(2) - PiR
    St = I.St; SRR, SRU, SUU = PiR @ St @ PiR, PiR @ St @ PiU, PiU @ St @ PiU
    SRRi = np.linalg.pinv(SRR); J = PiU - PiR @ SRRi @ SRU; schur = SUU - SRU.T @ SRRi @ SRU
    b = I.BA[i]
    return float(I.alpha[i] + b @ J.T @ I.lam), float(I.v[i] + b @ schur @ b)


def mk(a1, xm1, cap1, rate1=RATE, BAm=BA, BE=BE_SPAN, lam=LAM, **kw):
    alpha = np.array([a1, 0.0, 0.0]); xm = np.array([xm1, 0.05, 0.05]); cap = np.array([cap1, 0.25, 0.25])
    kp = np.array([rate1, RATE, RATE])
    return Inst(BAm, BE, alpha, V, kp, kp, xm, cap, lam=lam, **kw)


def retune(I, lam, PLm):
    I.lam = np.asarray(lam, float); I.St = SF + PLm
    I.bTB = np.linalg.solve(GAMMA * I.St, I.lam)
    I.mu = np.concatenate([I.alpha + I.BA @ I.lam, I.BE @ I.lam - I.cE]); I.Sig = I.B @ I.St @ I.B.T + I.Dres
    return I


def pt_spanning(args):
    curve, a1, xm1, cap1 = args
    I = mk(a1, xm1, cap1)
    r = classes(I); C, E = formula(I)
    return dict(curve=curve, a1=a1, xm1=xm1, cap1=cap1, fC=C, fE=E, **r)


def pt_unr(args):
    l2, a1, xm1, cap1 = args
    lam = np.array([LAM[0], l2])
    xEm = np.clip(np.linalg.solve(GAMMA * (SF + PL), lam)[0] - xm1 - 0.1, 0, 1)
    I = mk(a1, xm1, cap1, BAm=BA_UNR, BE=BE_UNR, lam=lam, xEm=xEm)
    r = classes(I); ared, sred = reduced(I); C, E = formula(I, reduced_fund=(ared, sred))
    return dict(curve=5, l2=l2, a1=a1, xm1=xm1, cap1=cap1, fC=C, fE=E, ared=ared, sred=sred, **r)


def pt_premia(idx):
    rng = np.random.default_rng([2032, 0, idx])
    lam = rng.uniform(-0.01, 0.04, 2); sds = rng.uniform(0.001, 0.01, 2)
    out = []
    for j in range(3):
        fr = np.random.default_rng([2032, 1, idx, j])
        alpha = fr.uniform(-0.01, 0.01, 3); kp = fr.uniform(0, 0.02, 3); km = fr.uniform(0, 0.02, 3)
        cap = fr.choice([0.1, 0.25, 1.0], 3); xm = np.minimum(fr.uniform(0, 0.25, 3), cap)
        I = retune(Inst(BA, BE_SPAN, alpha, V, kp, km, xm, cap, lam=lam), lam, np.diag(sds ** 2))
        I.xm[3:] = np.clip(np.linalg.solve(BE_SPAN.T, I.bTB - BA.T @ xm), 0, 1)
        r = classes(I); C, E = formula(I)
        out.append(dict(curve=3, idx=idx, j=j, fC=C, fE=E, **r))
    return out


def pt_fric(args):
    rE, fee, a1 = args
    I = mk(a1, 0.1, 0.25, kEp=rE, kEm=rE, cE=fee)
    r = classes(I); Cl, Cu, El, Eu = bracket(I, rE)
    return dict(curve=6, rE=rE, fee=fee, a1=a1, Cl=Cl, Cu=Cu, El=El, Eu=Eu, **r)


def main():
    t0 = time.time(); S = {}
    a_grid = [float(v) for v in np.round(np.linspace(-0.01, 0.03, 201), 6)]
    with mp.Pool(9) as pool:
        args = [(1, a, xm, cap) for a in a_grid for xm in (0.0, 0.1, 0.2) for cap in (0.25, 1.0)]
        args += [(2, a, float(xm), 0.25) for a in (0.002, 0.005, 0.01) for xm in np.round(np.linspace(0, 0.25, 101), 6)]
        args += [(4, a, float(xm), 0.25) for a in (-0.005, -0.0019, 0.0) for xm in np.round(np.linspace(0, 0.25, 101), 6)]
        S["spanning"] = pool.map(pt_spanning, args, chunksize=8); print("spanning", time.time() - t0, flush=True)
        S["premia"] = [r for rows in pool.map(pt_premia, range(200)) for r in rows]; print("premia", time.time() - t0, flush=True)
        S["unreachable"] = pool.map(pt_unr, [(l2, a, xm, cap) for l2 in (-0.01, 0.005, 0.02) for a in a_grid for xm in (0.0, 0.1, 0.2)
                                             for cap in (0.25, 1.0)], chunksize=8); print("unr", time.time() - t0, flush=True)
        S["frictions"] = pool.map(pt_fric, [(rE, fee, a) for rE in (0, 0.0005, 0.001, 0.0025, 0.005) for fee in (0, 0.0005, 0.001)
                                            for a in a_grid], chunksize=8); print("fric", time.time() - t0, flush=True)
    S["seconds"] = time.time() - t0
    json.dump(S, open(HERE / "summary.json", "w"), separators=(",", ":"), default=lambda o: o.tolist() if hasattr(o, "tolist") else str(o))
    print("done", S["seconds"])


if __name__ == "__main__":
    main()
