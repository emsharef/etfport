"""Experiment 037: claim 040 (the fund decision when ETFs sit at zero) against an independent one-review solver.
Registered design: experiments/037-d15d-etfs-at-zero-check.md.  Run: uv run python experiments/037/run.py

Solver: experiment 029's formulation (`Inst`, bp-scaled objectives, CLARABEL and OSQP), long-only ETFs with caps
removed (10) and a slack budget, frictionless spanning ETFs (fees allowed). Formula side: claim 040's Statement
(commit e88fd7ba), coded here: the at-zero set by complementarity, the fund marginal G_i with the slacks, the pieces
along one fund's trade, the drop-Z rule, and the premium-error shift.
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
Inst, GAMMA, SF, PL, LAM, V, SCALE = m29.Inst, m29.GAMMA, m29.SF, m29.PL, m29.LAM, m29.V, m29.SCALE
BA3 = m29.BA3
NAMED = {"equity-style": (-0.0019, 0.005), "fixed-income-style": (0.0020, 0.002)}
ZT = 1e-5            # an ETF is at zero when its holding is at most this (experiment 029's holding precision)


def opts(s):
    return dict(CLARABEL=dict(tol_gap_abs=1e-12, tol_gap_rel=1e-10, tol_feas=1e-10, max_iter=500),
                OSQP=dict(eps_abs=1e-10, eps_rel=1e-10, polish=True, max_iter=400000))[s]


def solve(I, solver="CLARABEL", fixA=None):
    n = I.n; x, up, um = cp.Variable(n), cp.Variable(n), cp.Variable(n)
    cons = [x == I.xm + up - um, up >= 0, um >= 0, x >= 0, x <= I.cap, cp.sum(up - um) + I.kp @ up + I.km @ um <= I.h]
    if fixA is not None:
        cons.append(x[:I.N] == fixA)
    obj = I.mu @ x - 0.5 * GAMMA * cp.quad_form(x, cp.psd_wrap(I.Sig)) - (I.kp @ up + I.km @ um)
    p = cp.Problem(cp.Maximize(SCALE * obj), cons); p.solve(solver=solver, **opts(solver))
    return x.value, p.status


def mk(BA, BE, alpha, v, kp, km, xm, lam=LAM, PLm=None, cE=0.0, xEm=None, cap=0.25):
    N, M = np.atleast_2d(BA).shape[0], np.atleast_2d(BE).shape[0]
    I = Inst(BA, BE, alpha, v, kp, km, xm, cap, lam=lam, cE=cE, capE=10.0, h=10.0,
             xEm=np.zeros(M) if xEm is None else xEm)
    if PLm is not None:
        I.St = SF[:I.BE.shape[1], :I.BE.shape[1]] + PLm
        I.bTB = np.linalg.solve(GAMMA * I.St, I.lam)
        I.mu = np.concatenate([I.alpha + I.BA @ I.lam, I.BE @ I.lam - I.cE]); I.Sig = I.B @ I.St @ I.B.T + I.Dres
    return I


# ---------------------------------------------------------------- formula side (claim 040) ----------
def pieces(I):
    R = np.linalg.inv(I.BE); Q = R.T @ I.BA.T                          # M x N, column r_i
    muE = I.BE @ I.lam - I.cE; SEE = I.BE @ I.St @ I.BE.T
    return Q, muE, SEE


def at_zero(I, q):
    """Part 2: the at-zero set Z(q) by enumeration of candidate sets; returns (Z, w, zeta, margin)."""
    Q, muE, SEE = pieces(I); M = len(muE)
    found = []
    for bits in itertools.product([0, 1], repeat=M):
        Z = [j for j in range(M) if bits[j]]; c = [j for j in range(M) if not bits[j]]
        w = np.array(q, float).copy(); zeta = np.zeros(M)
        if c:
            Scc = SEE[np.ix_(c, c)]
            w[c] = np.linalg.solve(Scc, muE[c] / GAMMA - (SEE[np.ix_(c, Z)] @ q[Z] if Z else 0))
        if Z:
            SZc = SEE[np.ix_(Z, c)] if c else np.zeros((len(Z), 0))
            Szz = SEE[np.ix_(Z, Z)] - (SZc @ np.linalg.solve(SEE[np.ix_(c, c)], SZc.T) if c else 0)
            muz = muE[Z] - (SZc @ np.linalg.solve(SEE[np.ix_(c, c)], muE[c]) if c else 0)
            zeta[Z] = GAMMA * Szz @ q[Z] - muz
        ok_z = np.all(zeta[Z] >= -1e-12) if Z else True
        ok_c = np.all(w[c] >= q[c] - 1e-12) if c else True
        if ok_z and ok_c:
            margin = min([np.min(np.abs(zeta[Z]))] if Z else [np.inf] + []) if Z else np.inf
            margin = min(margin, np.min(np.abs(w[c] - q[c])) if c else np.inf)
            found.append((tuple(Z), w, zeta, margin))
    Z, w, zeta, margin = found[0]
    return Z, w, zeta, float(margin), len(found)


def G_formula(I, xA):
    Q, _, _ = pieces(I)
    Z, w, zeta, margin, nsets = at_zero(I, Q @ xA)
    at = I.alpha + Q.T @ I.cE                                         # alpha~ = alpha_hat + Q' c^E
    return at - GAMMA * I.v * xA - Q.T @ zeta, Z, zeta, margin


def sZ(I, Z, i=0):
    Q, _, SEE = pieces(I); M = SEE.shape[0]
    c = [j for j in range(M) if j not in Z]; Z = list(Z)
    if not Z:
        return I.v[i]
    SZc = SEE[np.ix_(Z, c)] if c else np.zeros((len(Z), 0))
    Szz = SEE[np.ix_(Z, Z)] - (SZc @ np.linalg.solve(SEE[np.ix_(c, c)], SZc.T) if c else 0)
    r = Q[Z, i]
    return float(I.v[i] + r @ Szz @ r)


# ---------------------------------------------------------------- checks ----------
def classify(tr):
    return "buy" if tr > ZT else ("sell" if tr < -ZT else "hold")


def check_instance(I, tag):
    """Parts 1-3 at one instance: solve, then compare the formulas."""
    x, st = solve(I); xo, st2 = solve(I, "OSQP")
    N, M = I.N, I.n - I.N
    Q, muE, SEE = pieces(I)
    g = I.g(x)
    zeta_sol = np.where(x[N:] <= ZT, np.maximum(0.0, -g[N:]), 0.0)
    Zsol = tuple(j for j in range(M) if x[N + j] <= ZT)
    Zf, wf, zf, margin, nsets = at_zero(I, Q @ x[:N])
    # part 1: fund lines with the solver's slacks (eta = 0, frictionless ETFs)
    Gsol = I.alpha + Q.T @ I.cE - GAMMA * I.v * x[:N] - Q.T @ zeta_sol
    p1 = True
    for i in range(N):
        tr = x[i] - I.xm[i]; at0, atc = x[i] <= ZT, x[i] >= I.cap[i] - ZT
        if tr > ZT and not atc:
            p1 &= abs(Gsol[i] - I.kp[i]) < 1e-7
        elif tr > ZT and atc:
            p1 &= Gsol[i] >= I.kp[i] - 1e-7
        elif tr < -ZT and not at0:
            p1 &= abs(Gsol[i] + I.km[i]) < 1e-7
        elif tr < -ZT and at0:
            p1 &= Gsol[i] <= -I.km[i] + 1e-7
        else:
            lo_ok = Gsol[i] >= -I.km[i] - 1e-7 or at0
            hi_ok = Gsol[i] <= I.kp[i] + 1e-7 or atc
            p1 &= bool(lo_ok and hi_ok)
    interior_etf_ok = bool(np.all(np.abs(g[N:][x[N:] > ZT]) < 1e-7))
    # part 3(a): hold test at the incumbent
    Gm, Zm, _, marg_m = G_formula(I, I.xm[:N])
    hold_pred = all((Gm[i] <= I.kp[i] or I.xm[i] >= I.cap[i]) and (Gm[i] >= -I.km[i] or I.xm[i] <= 0) for i in range(N))
    hold_sol = not np.any(np.abs(x[:N] - I.xm[:N]) > ZT)
    # 3(c) for N = 1
    dec = pred = None
    if N == 1:
        dec = classify(x[0] - I.xm[0])
        pred = "buy" if (Gm[0] > I.kp[0] and I.xm[0] < I.cap[0]) else ("sell" if (Gm[0] < -I.km[0] and I.xm[0] > 0) else "hold")
    edge = margin < 1e-6 or marg_m < 1e-6 or (N == 1 and min(abs(Gm[0] - I.kp[0]), abs(Gm[0] + I.km[0])) < 1e-7)
    return dict(tag=tag, N=N, M=M, Zsol=list(Zsol), Zf=[int(j) for j in Zf], zeta_err=float(np.max(np.abs(zeta_sol - zf))), nsets=nsets,
                p1=bool(p1), etf_int_ok=interior_etf_ok, hold_pred=bool(hold_pred), hold_sol=bool(hold_sol), dec=dec, pred=pred,
                edge=bool(edge), slack=bool(I.cash(x) > 1e-5 and np.all(x[N:] < 10 - 1e-5)), dx=float(np.max(np.abs(x - xo))), status=[st, st2])


def draw_inst(idx):
    rng = np.random.default_rng([2037, 0, idx])
    alpha = rng.uniform(-0.01, 0.01, 3); v = 0.02 ** 2 * (1 + rng.uniform(0.01, 3, 3))
    kp, km = rng.uniform(0, 0.02, 3), rng.uniform(0, 0.02, 3); xm = rng.uniform(0, 0.25, 3)
    lam = rng.uniform(-0.01, 0.03, 2); sds = rng.uniform(0.001, 0.01, 2); cE = rng.uniform(0, 0.002, 2)
    return mk(BA3, np.eye(2), alpha, v, kp, km, xm, lam=lam, PLm=np.diag(sds ** 2), cE=cE, xEm=rng.uniform(0, 1, 2))


def draw(idx):
    return check_instance(draw_inst(idx), f"draw{idx}")


def one_etf(idx):
    """Part 5(a): K = M = 1, market ETF, fund loadings 1."""
    rng = np.random.default_rng([2037, 2, idx])
    N = int(rng.integers(1, 4))
    alpha = rng.uniform(-0.01, 0.01, N); kp, km = rng.uniform(0, 0.01, N), rng.uniform(0, 0.01, N); xm = rng.uniform(0, 0.25, N)
    lam = np.array([rng.uniform(-0.005, 0.02)]); cE = rng.uniform(0, 0.002)
    sf, pl = m29.SF, m29.PL                                           # one factor: 029's Inst reads these module globals
    m29.SF, m29.PL = np.array([[0.08 ** 2]]), np.array([[0.005 ** 2]])
    try:
        I = Inst(np.ones((N, 1)), np.eye(1), alpha, V, kp, km, xm, 0.25, lam=lam, cE=cE, capE=10.0, h=10.0, xEm=np.zeros(1))
    finally:
        m29.SF, m29.PL = sf, pl
    x, _ = solve(I)
    q = float(np.sum(x[:N])); muE = float(lam[0] - cE); sEE = float(I.St[0, 0])
    return dict(N=N, at_zero_sol=bool(x[N] <= ZT), at_zero_rule=bool(muE <= GAMMA * sEE * q), margin=abs(muE - GAMMA * sEE * q))


def sweep(args):
    """Named-point sweeps with one fund (loading (1, 0.5)): parts 3(c), 4 and 3(d)."""
    name, kind, val = args
    a0, rate = NAMED[name]
    lam = np.array([LAM[0], val]) if kind == "lam2" else LAM
    xm = val if kind == "xm" else 0.1
    I = mk(np.array([[1.0, 0.5]]), np.eye(2), a0, V, rate, rate, xm, lam=lam)
    base = check_instance(I, f"{name}-{kind}-{val}")
    x, _ = solve(I)
    # part 4: the pieces along the fund's trade (formula) and the solver's marginal on a fine x grid
    Q, _, _ = pieces(I)
    xs = np.linspace(0, 0.25, 101)
    Gs, Zs = [], []
    for xa in xs:
        xf, _ = solve(I, fixA=np.array([xa]))
        gE = I.g(xf)[1:]
        zeta = np.where(xf[1:] <= ZT, np.maximum(0.0, -gE), 0.0)
        Gs.append(float(I.alpha[0] + Q[:, 0] @ I.cE - GAMMA * I.v[0] * xa - Q[:, 0] @ zeta)); Zs.append(tuple(j for j in range(2) if xf[1 + j] <= ZT))
    Gf = [float(G_formula(I, np.array([xa]))[0][0]) for xa in xs]
    Zf = [G_formula(I, np.array([xa]))[1] for xa in xs]
    slopes = []
    for k in range(len(xs) - 1):
        if Zf[k] == Zf[k + 1]:
            slopes.append(abs((Gs[k + 1] - Gs[k]) / (xs[k + 1] - xs[k]) + GAMMA * sZ(I, Zf[k])))
    # drop-Z rule
    Gm, Zm, _, _ = G_formula(I, np.array([xm]))
    s0 = sZ(I, Zm); aZ = Gm[0] + GAMMA * s0 * xm
    xt = float(np.clip(np.clip(xm, (aZ - rate) / (GAMMA * s0), (aZ + rate) / (GAMMA * s0)), 0, 0.25))
    xt_u = float(np.clip(xm, (aZ - rate) / (GAMMA * s0), (aZ + rate) / (GAMMA * s0)))
    in_piece = G_formula(I, np.array([min(max(xt, 0.0), 0.25)]))[1] == Zm
    same_bound = (xt in (0.0, 0.25)) and abs(x[0] - xt) < 1e-5
    # part 3(d): premium-error shift of G at fixed holdings, and of a trading fund's holding
    shifts = []
    for k, s in itertools.product(range(2), (-1, 1)):
        e = np.zeros(2); e[k] = s * 1e-4
        Ie = mk(np.array([[1.0, 0.5]]), np.eye(2), a0, V, rate, rate, xm, lam=lam + e)
        xf_e, _ = solve(Ie, fixA=np.array([x[0]])); xf_0, _ = solve(I, fixA=np.array([x[0]]))
        zs = lambda Ix, xx: np.where(xx[1:] <= ZT, np.maximum(0.0, -Ix.g(xx)[1:]), 0.0)
        dG_sol = float(-Q[:, 0] @ (zs(Ie, xf_e) - zs(I, xf_0)))
        _, Z0, _, _ = G_formula(I, np.array([x[0]])); Z0 = list(Z0)
        M_ = 2; c = [j for j in range(M_) if j not in Z0]
        _, _, SEE = pieces(I)
        if Z0:
            BZc = I.BE[Z0] - (SEE[np.ix_(Z0, c)] @ np.linalg.solve(SEE[np.ix_(c, c)], I.BE[c]) if c else 0)
            dG_f = float(Q[Z0, 0] @ BZc @ e)
        else:
            dG_f = 0.0
        xe, _ = solve(Ie)
        trading = abs(x[0] - xm) > ZT and 1e-5 < x[0] < 0.25 - 1e-5
        same_Z = G_formula(Ie, np.array([xe[0]]))[1] == tuple(Z0)
        Z_e = list(G_formula(Ie, np.array([x[0]]))[1])
        crosses = (xe[0] - xm) * (x[0] - xm) <= 0 or abs(xe[0] - xm) <= ZT
        shifts.append(dict(e=[k, s], dG_sol=dG_sol, dG_f=dG_f, Z=Z0, Z_e=Z_e, crosses=bool(crosses), dx_sol=float(xe[0] - x[0]),
                           dx_f=float(dG_f / (GAMMA * sZ(I, tuple(Z0)))) if (trading and same_Z) else None))
    return dict(name=name, kind=kind, val=val, base=base, G_err=float(np.max(np.abs(np.array(Gs) - np.array(Gf)))),
                Z_agree=int(sum(a == b for a, b in zip(Zs, Zf))), npts=len(xs), slope_err=float(max(slopes)) if slopes else None,
                pieces=len(set(Zf)), x_sol=float(x[0]), x_drop=xt, x_drop_u=xt_u, in_piece=bool(in_piece), same_bound=bool(same_bound),
                Zm=list(Zm), Zopt=list(G_formula(I, np.array([x[0]]))[1]), s_m=s0, s_opt=sZ(I, G_formula(I, np.array([x[0]]))[1]), shifts=shifts)


def part4_inst(idx):
    rng = np.random.default_rng([2037, 3, idx])
    a0 = rng.uniform(-0.003, 0.008); l2 = rng.uniform(-0.002, 0.005); xm = rng.uniform(0, 0.25); CAP4 = 2.0
    kp, km = rng.uniform(0, 0.005), rng.uniform(0, 0.005); cE = rng.uniform(0, 0.001, 2)
    return mk(np.array([[1.0, 0.5]]), np.eye(2), a0, V, kp, km, xm, lam=np.array([LAM[0], l2]), cE=cE, cap=CAP4), CAP4


def fold_in(args):
    """Part 5(d) (approved Statement, f62b0fb9): with the at-zero ETFs' slacks zeta taken as given at the constrained
    optimum, that optimum is the unconstrained one (ETFs free) for the premium vector (alpha~ - Q_Z' zeta_Z, mu_E + zeta).
    The pre-fix sign (mu_E - zeta) is run alongside for contrast."""
    kind, idx = args
    I = draw_inst(idx) if kind == "draw" else part4_inst(idx)[0]
    x, _ = solve(I)
    N, M = I.N, I.n - I.N
    if not (I.cash(x) > 1e-5 and np.all(x[N:] < 10 - 1e-5)):
        return dict(kind=kind, idx=idx, ok=False)
    Q, muE, _ = pieces(I)
    g = I.g(x)
    zeta = np.where(x[N:] <= ZT, np.maximum(0.0, -g[N:]), 0.0)
    if not np.any(x[N:] <= ZT):
        return dict(kind=kind, idx=idx, ok=True, Z=False)
    at = I.alpha + Q.T @ I.cE
    out = dict(kind=kind, idx=idx, ok=True, Z=True, nZ=int(np.sum(x[N:] <= ZT)), zeta_max=float(zeta.max()))
    for tag, sgn in (("fold", +1.0), ("old_sign", -1.0)):
        at2 = at - Q.T @ zeta if tag == "fold" else at - Q.T @ zeta
        muE2 = muE + sgn * zeta
        mu = np.concatenate([at2 + Q.T @ muE2, muE2])              # instrument means from (alpha~', mu_E'): B^A lambda = Q' B^E lambda
        n = I.n; y, up, um = cp.Variable(n), cp.Variable(n), cp.Variable(n)
        lb = np.concatenate([np.zeros(N), np.full(M, -10.0)])      # ETFs free (bounds far away)
        cons = [y == I.xm + up - um, up >= 0, um >= 0, y >= lb, y <= I.cap, cp.sum(up - um) + I.kp @ up + I.km @ um <= I.h]
        obj = mu @ y - 0.5 * GAMMA * cp.quad_form(y, cp.psd_wrap(I.Sig)) - (I.kp @ up + I.km @ um)
        cp.Problem(cp.Maximize(SCALE * obj), cons).solve(solver="CLARABEL", **opts("CLARABEL"))
        out[f"{tag}_dx"] = float(np.max(np.abs(y.value - x)))
        out[f"{tag}_min_etf"] = float(y.value[N:].min())
    return out


def part4_draw(idx):
    """Deviation 2: one fund whose trade can cross a piece boundary (the second ETF near zero)."""
    I, CAP4 = part4_inst(idx); xm, kp, km = I.xm[0], I.kp[0], I.km[0]
    x, st = solve(I)
    if not (I.cash(x) > 1e-5 and all(v < 10 - 1e-5 for v in x[1:])):
        return dict(idx=idx, ok=False)
    Gm, Zm, _, marg = G_formula(I, np.array([xm]))
    s0 = sZ(I, Zm); aZ = Gm[0] + GAMMA * s0 * xm
    xu = float(np.clip(xm, (aZ - kp) / (GAMMA * s0), (aZ + km) / (GAMMA * s0))); xt = float(np.clip(xu, 0, CAP4))
    seg = np.linspace(xm, xu, 400)
    Zs = [G_formula(I, np.array([v]))[1] for v in seg]
    in_piece = all(z == Zm for z in Zs)
    changes = []
    for k in range(1, len(seg)):
        if Zs[k] != Zs[k - 1]:
            changes.append(float(np.sign(sZ(I, Zs[k]) - sZ(I, Zs[k - 1]))))
    both_same_bound = (abs(x[0] - xt) < 1e-5) and (xt <= 1e-9 or xt >= CAP4 - 1e-9)
    return dict(idx=idx, ok=True, cap=CAP4, xm=xm, x=float(x[0]), xt=xt, xu=xu, in_piece=bool(in_piece), changes=changes, both_same_bound=bool(both_same_bound),
                edge=bool(marg < 1e-6 or min(abs(Gm[0] - kp), abs(Gm[0] + km)) < 1e-7))


def main():
    t0 = time.time(); S = {}
    with mp.Pool(9) as pool:
        S["draws"] = pool.map(draw, range(500)); print("draws", time.time() - t0, flush=True)
        S["one_etf"] = pool.map(one_etf, range(300)); print("one", time.time() - t0, flush=True)
        S["part4"] = pool.map(part4_draw, range(500)); print("p4", time.time() - t0, flush=True)
        args = [(nm, "lam2", float(v)) for nm in NAMED for v in np.round(np.linspace(-0.01, 0.02, 121), 6)]
        args += [(nm, "xm", float(v)) for nm in NAMED for v in np.round(np.linspace(0, 0.25, 51), 6)]
        S["sweeps"] = pool.map(sweep, args, chunksize=2); print("sweeps", time.time() - t0, flush=True)
    S["seconds"] = time.time() - t0
    json.dump(S, open(HERE / "summary.json", "w"), separators=(",", ":"), default=lambda o: o.tolist() if hasattr(o, "tolist") else (int(o) if isinstance(o, np.integer) else float(o)))
    print("done", S["seconds"])


def main5d():
    """Adds part 5(d) to summary.json (the rest of the run is unchanged)."""
    S = json.load(open(HERE / "summary.json"))
    with mp.Pool(9) as pool:
        S["part5d"] = pool.map(fold_in, [("draw", i) for i in range(500)] + [("part4", i) for i in range(500)])
    json.dump(S, open(HERE / "summary.json", "w"), separators=(",", ":"), default=lambda o: o.tolist() if hasattr(o, "tolist") else (int(o) if isinstance(o, np.integer) else float(o)))
    print("5d done")


if __name__ == "__main__":
    import sys as _sys
    main5d() if _sys.argv[1:] == ["5d"] else main()
