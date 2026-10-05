"""Experiment 030: claim 105 (premium error in fund choice, one review, M7) against an independent one-review solver.
Registered design: experiments/030-criterion-d-check.md.  Run: uv run python experiments/030/run.py

Uses experiment 029's one-review formulation (`Inst`, objectives in bp units, CLARABEL and OSQP). Formula side:
claim 105's Statement (reduced moments through the hedge map J and the Schur complement), coded here.
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
SOLVERS = m29.SOLVERS
BA_SPAN = m29.BA3
BE_SPAN = np.eye(2)                                    # Deviation 1 (as experiment 029's Deviation 1)
BA_UNR = np.array([[1.0, 0.5], [1.0, 0.0], [1.0, 0.0]])
BE_UNR = np.array([[1.0, 0.0]])
NAMED = {"equity-style": (-0.0019, 0.005), "fixed-income-style": (0.0020, 0.002)}   # alpha_hat, fund rate
SD = 0.005
TRADE = 1e-5                                           # Deviation 2: trade-sign tolerance at the solver's position precision


def opts(solver):
    return dict(CLARABEL=dict(tol_gap_abs=1e-12, tol_gap_rel=1e-10, tol_feas=1e-10, max_iter=500),
                OSQP=dict(eps_abs=1e-10, eps_rel=1e-10, polish=True, max_iter=400000))[solver]


def retune(I, lam=None, PLm=None):
    """Re-set the premium belief (mean, covariance) of an instance, keeping its incumbents."""
    if lam is not None:
        I.lam = np.asarray(lam, float)
    if PLm is not None:
        I.St = SF + PLm
    I.bTB = np.linalg.solve(GAMMA * I.St, I.lam)
    I.mu = np.concatenate([I.alpha + I.BA @ I.lam, I.BE @ I.lam - I.cE])
    I.Sig = I.B @ I.St @ I.B.T + I.Dres
    return I


def joint(I, solver, fixA=None, lbE=0.0):
    """max Q over F (funds optionally fixed at fixA; ETF lower bound lbE). Returns (x, Q(x), eta, status)."""
    n = I.n; x, up, um = cp.Variable(n), cp.Variable(n), cp.Variable(n)
    lb = np.concatenate([np.zeros(I.N), np.full(I.M, lbE)])
    cons = [x == I.xm + up - um, up >= 0, um >= 0, x >= lb, x <= I.cap]
    if fixA is not None:
        cons.append(x[:I.N] == fixA)
    cons.append(cp.sum(up - um) + I.kp @ up + I.km @ um <= I.h)
    obj = I.mu @ x - 0.5 * GAMMA * cp.quad_form(x, cp.psd_wrap(I.Sig)) - (I.kp @ up + I.km @ um)
    p = cp.Problem(cp.Maximize(SCALE * obj), cons); p.solve(solver=solver, **opts(solver))
    eta = float(cons[-1].dual_value) / SCALE if cons[-1].dual_value is not None else None
    return x.value, I.Q(x.value), eta, p.status


def both(I, **kw):
    a = joint(I, "CLARABEL", **kw); b = joint(I, "OSQP", **kw)
    return a, dict(dQ=abs(a[1] - b[1]), dx=float(np.abs(a[0] - b[0]).max()), status=[a[3], b[3]])


def slack(I, x, lbE=0.0):
    xe = x[I.N:]
    return bool(np.all(xe > lbE + INTERIOR) and np.all(xe < I.cap[I.N:] - INTERIOR) and I.cash(x) > INTERIOR)


def reduced(I, i=0):
    """Claim 105's reduced moments for fund i (hedge map J and Schur complement of Sigma~_f)."""
    Q_, _ = np.linalg.qr(I.BE.T); PiR = Q_ @ Q_.T; PiU = np.eye(2) - PiR
    St = I.St; SRR, SRU, SUU = PiR @ St @ PiR, PiR @ St @ PiU, PiU @ St @ PiU
    SRRi = np.linalg.pinv(SRR); J = PiU - PiR @ SRRi @ SRU; schur = SUU - SRU.T @ SRRi @ SRU
    b = I.BA[i]
    return J, float(I.alpha[i] + b @ J.T @ I.lam), float(I.v[i] + b @ schur @ b)


def band_hold(ared, sred, I, i=0):
    kp, km, xm, cap = I.kp[i], I.km[i], I.xm[i], I.cap[i]
    return float(np.clip(np.clip(xm, (ared - kp) / (GAMMA * sred), (ared + km) / (GAMMA * sred)), 0, cap))


def psi(a, ared, sred, I, i=0):
    return ared * a - 0.5 * GAMMA * sred * a ** 2 - I.kp[i] * max(a - I.xm[i], 0) - I.km[i] * max(I.xm[i] - a, 0)


def unr_inst(a0, rate, xm, cap, lam=LAM):
    alpha = np.array([a0, GAMMA * V * 0.1, GAMMA * V * 0.1])
    xEm = np.clip(np.linalg.solve(GAMMA * (SF + PL), lam)[0] - xm - 0.2, 0, 1)
    return Inst(BA_UNR, BE_UNR, alpha, V, [rate, 0.002, 0.002], [rate, 0.002, 0.002], [xm, 0.1, 0.1], [cap, 0.25, 0.25],
                lam=lam, xEm=xEm)


# ---------------------------------------------------------------- curve 1: part 1 ----------
def c1(idx):
    rng = np.random.default_rng([2030, 0, idx])
    alpha = rng.uniform(-0.01, 0.01, 3); v = 0.02 ** 2 * (1 + rng.uniform(0.01, 3, 3))
    kp, km = rng.uniform(0, 0.02, 3), rng.uniform(0, 0.02, 3)
    cap = rng.choice([0.1, 0.25, 1.0], 3); xm = np.minimum(rng.uniform(0, 0.25, 3), cap)
    lam = rng.uniform(-0.01, 0.04, 2); sds = rng.uniform(0.001, 0.01, 2); PLm = np.diag(sds ** 2)
    I = retune(Inst(BA_SPAN, BE_SPAN, alpha, v, kp, km, xm, cap, lam=lam), PLm=PLm)
    base, d0 = both(I); ok = slack(I, base[0]); out = dict(idx=idx, rows=[], hyp=ok, dQ=d0["dQ"], dx=d0["dx"], status=d0["status"])
    for k, s in itertools.product(range(2), (-1, 1)):
        dl = np.zeros(2); dl[k] = s * sds[k]
        J2 = retune(Inst(BA_SPAN, BE_SPAN, alpha, v, kp, km, xm, cap, lam=lam, xEm=I.xm[3:]), lam=lam + dl, PLm=PLm)
        r, d = both(J2)
        dy = (r[0] - base[0]) @ I.B - np.linalg.solve(GAMMA * I.St, dl)
        out["rows"].append(dict(shift=[k, s], hyp=slack(J2, r[0]), fundL1=float(np.abs(r[0][:3] - base[0][:3]).sum()),
                                expo_err=float(np.abs(dy).max()), dQ=d["dQ"], dx=d["dx"], status=d["status"]))
    return out


# ---------------------------------------------------------------- curves 2-4 ----------
def c234(args):
    name, rate, xm, cap, l2 = args
    a0 = NAMED[name][0]
    lam = np.array([LAM[0], l2])
    I = unr_inst(a0, rate, xm, cap, lam=lam)
    (xJ, QJ, eta, _), d = both(I)
    J_, ared, sred = reduced(I)
    f = band_hold(ared, sred, I)
    # gradient in lambda_hat_2 by central differences, step 1e-4 (Deviation 2)
    h = 1e-4; xs = []
    for s in (-1, 1):
        Ih = retune(unr_inst(a0, rate, xm, cap, lam=lam), lam=lam + np.array([0, s * h]))
        Ih.xm = I.xm.copy(); Ih = retune(Ih)
        xs.append(joint(Ih, "CLARABEL")[0][0])
    grad = (xs[1] - xs[0]) / (2 * h)
    def regime(A):
        f_ = band_hold(A, sred, I)
        pc = "buy" if (A - I.kp[0]) / (GAMMA * sred) > I.xm[0] else ("sell" if (A + I.km[0]) / (GAMMA * sred) < I.xm[0] else "hold")
        return pc, f_ <= 0 or f_ >= cap
    dA = float((J_ @ I.BA[0]) @ np.array([0, h]))
    rg = regime(ared)
    gform = 0.0 if (rg[0] == "hold" or rg[1]) else float((J_ @ I.BA[0])[1] / (GAMMA * sred))
    row = dict(name=name, rate=rate, xm=xm, cap=cap, l2=l2, hyp=slack(I, xJ), x1=float(xJ[0]), f_hold=f, grad=float(grad), f_grad=gform,
               grad_ok_region=bool(regime(ared - dA) == rg == regime(ared + dA)),
               dQ=d["dQ"], dx=d["dx"], status=d["status"], errs=[])
    m = ared - GAMMA * sred * xm
    if not (-I.km[0] <= m <= I.kp[0]) or not row["hyp"]:
        return row
    # curve 3 and 4: held at the truth; errors e = t (0, 1)
    true_trade = xJ[0] - xm
    for t in np.round(np.linspace(-0.03, 0.03, 41), 6):
        e = np.array([0.0, t]); delta = float(I.BA[0] @ J_.T @ e)
        Ie = unr_inst(a0, rate, xm, cap, lam=lam); Ie.xm = I.xm.copy(); Ie = retune(Ie, lam=lam + e)
        (xe, _, _, _), de = both(Ie)
        tr = xe[0] - xm
        dec = "buy" if tr > TRADE else ("sell" if tr < -TRADE else "hold")
        pred = "buy" if (m + delta > I.kp[0] and xm < cap) else ("sell" if (m + delta < -I.km[0] and xm > 0) else "hold")
        edge = min(abs(m + delta - I.kp[0]), abs(m + delta + I.km[0])) < 1e-7
        # loss of the fund decision at the truth, ETFs re-optimized (Deviation 3)
        (xf, Qf, _, _) = joint(I, "CLARABEL", fixA=xe[:3])
        loss = QJ - Qf
        Dl = float(xe[0] - xJ[0])
        mJ = ared - GAMMA * sred * xJ[0]; muJ = max(0.0, mJ - I.kp[0], -I.km[0] - mJ)
        upper = 0.5 * GAMMA * sred * Dl ** 2 + (I.kp[0] + I.km[0] + muJ) * abs(Dl)
        row["errs"].append(dict(t=float(t), delta=delta, dec=dec, pred=pred, edge=bool(edge), hyp=slack(Ie, xe) and slack(I, xf),
                                loss=float(loss), upper=float(upper), D=Dl, Dbound=abs(delta) / (GAMMA * sred), dQ=de["dQ"]))
    return row


# ---------------------------------------------------------------- curve 4: expected loss ----------
def mc_chunk(args):
    name, xm, cap, seeds = args
    a0, rate = NAMED[name]
    I = unr_inst(a0, rate, xm, cap)
    xJ, QJ, _, _ = joint(I, "CLARABEL")
    out = []
    for sd in seeds:
        e = np.random.default_rng([2030, 1, sd]).standard_normal(2) * SD
        Ie = unr_inst(a0, rate, xm, cap); Ie.xm = I.xm.copy(); Ie = retune(Ie, lam=LAM + e)
        xe = joint(Ie, "CLARABEL")[0]
        Qf = joint(I, "CLARABEL", fixA=xe[:3])[1]
        rec = [float(QJ - Qf)]
        if sd < 500:
            xo = joint(Ie, "OSQP")[0]; Qo = joint(I, "OSQP", fixA=xo[:3])[1]; rec.append(float(abs((QJ - Qf) - (joint(I, "OSQP")[1] - Qo))))
        out.append(rec)
    return out


# ---------------------------------------------------------------- curve 5: naive rule ----------
def naive_hold(I, i, solver="CLARABEL"):
    b = I.BA[i]; muh = I.alpha[i] + b @ I.lam; s2 = I.v[i] + b @ I.St @ b
    a, up, um = cp.Variable(), cp.Variable(), cp.Variable()
    p = cp.Problem(cp.Maximize(SCALE * (muh * a - 0.5 * GAMMA * s2 * cp.square(a) - I.kp[i] * up - I.km[i] * um)),
                   [a == I.xm[i] + up - um, up >= 0, um >= 0, a >= 0, a <= I.cap[i]])
    p.solve(solver=solver, **opts(solver))
    form = float(np.clip(np.clip(I.xm[i], (muh - I.kp[i]) / (GAMMA * s2), (muh + I.km[i]) / (GAMMA * s2)), 0, I.cap[i]))
    return float(a.value), form


def naive_eval(I):
    (xJ, QJ, _, _), d = both(I)
    hs = [naive_hold(I, i) for i in range(I.N)]
    an = np.array([h[0] for h in hs])
    xf, Qf, _, _ = joint(I, "CLARABEL", fixA=an)
    xo, Qo, _, _ = joint(I, "OSQP", fixA=np.array([naive_hold(I, i, "OSQP")[0] for i in range(I.N)]))
    ab = [band_hold(I.alpha[i], I.v[i], I, i) for i in range(I.N)]
    form = sum(psi(ab[i], I.alpha[i], I.v[i], I, i) - psi(hs[i][1], I.alpha[i], I.v[i], I, i) for i in range(I.N))
    neg_bought = int(sum(I.alpha[i] < 0 and an[i] > I.xm[i] + TRADE for i in range(I.N)))
    return dict(loss=float(QJ - Qf), form=float(form), hold_err=float(max(abs(h[0] - h[1]) for h in hs)),
                hyp=slack(I, xJ) and slack(I, xf), neg_bought=neg_bought, dQ=float(max(d["dQ"], abs(Qf - Qo))), dx=d["dx"])


def c5_draw(idx):
    rng = np.random.default_rng([2030, 0, idx])
    alpha = rng.uniform(-0.01, 0.01, 3); v = 0.02 ** 2 * (1 + rng.uniform(0.01, 3, 3))
    kp, km = rng.uniform(0, 0.02, 3), rng.uniform(0, 0.02, 3)
    cap = rng.choice([0.1, 0.25, 1.0], 3); xm = np.minimum(rng.uniform(0, 0.25, 3), cap)
    lam = rng.uniform(-0.01, 0.04, 2); sds = rng.uniform(0.001, 0.01, 2)
    I = retune(Inst(BA_SPAN, BE_SPAN, alpha, v, kp, km, xm, cap, lam=lam), PLm=np.diag(sds ** 2))
    return dict(idx=idx, **naive_eval(I))


def c5_sweep(args):
    name, l1 = args
    a0, rate = NAMED[name]
    I = Inst(BA_SPAN, BE_SPAN, a0, V, rate, rate, 0.1, 0.25, lam=np.array([l1, LAM[1]]))
    return dict(name=name, l1=l1, **naive_eval(I))


# ---------------------------------------------------------------- curve 6: outside the hypotheses ----------
def c6(args):
    """Deviation 5: each shifted optimum is classified (ETF at a bound, budget binding); 'relaxed' removes the ETF bounds
    (lower -1, cap 2) to isolate red's bound channel from the cost channel."""
    name, kind, level, relaxed = args
    a0, rate = NAMED[name]
    lbE, capE = (-1.0, 2.0) if relaxed else (0.0, 1.0)
    kw = dict(kEp=level, kEm=level) if kind == "etf_rate" else dict(h=level, xEm=np.zeros(2))
    mk = lambda: Inst(BA_SPAN, BE_SPAN, a0, V, rate, rate, 0.1, 0.25, capE=capE, **kw)
    I = mk()
    (x0, _, eta0, _), d = both(I, lbE=lbE)
    def flags(Ix, x, eta):
        xe = x[3:]
        return bool(np.any(xe < lbE + INTERIOR) or np.any(xe > capE - INTERIOR)), bool((eta or 0) > 1e-9)
    shifts = []
    for k, s in itertools.product(range(2), (-1, 1)):
        Ie = mk(); Ie.xm = I.xm.copy(); Ie = retune(Ie, lam=LAM + s * SD * np.eye(2)[k])
        xs, _, eta, _ = joint(Ie, "CLARABEL", lbE=lbE)
        b_, e_ = flags(Ie, xs, eta)
        shifts.append(dict(shift=[k, s], L1=float(np.abs(xs[:3] - x0[:3]).sum()), etf_bound=b_, budget=e_))
    b0, e0 = flags(I, x0, eta0)
    clean = [sh["L1"] for sh in shifts if not sh["etf_bound"] and not sh["budget"]]
    return dict(name=name, kind=kind, level=level, relaxed=relaxed, base_etf_bound=b0, base_budget=e0, eta=eta0, dQ=d["dQ"],
                L1_all=max(sh["L1"] for sh in shifts), L1_clean=max(clean) if (clean and not b0 and not e0) else None,
                n_clean=len(clean), shifts=shifts, x=[float(v) for v in x0])


def rounded(o):
    """Floats to 10 significant digits (the checks use at most about 1e-10 relative)."""
    if isinstance(o, float):
        return float(f"{o:.10g}")
    if isinstance(o, dict):
        return {k: rounded(v) for k, v in o.items()}
    if isinstance(o, (list, tuple)):
        return [rounded(v) for v in o]
    return o


def main():
    t0 = time.time(); S = {}
    with mp.Pool(9) as pool:
        S["c1"] = pool.map(c1, range(200)); print("c1", time.time() - t0, flush=True)
        args = [(nm, rt, xm, cap, float(l2)) for nm in NAMED for rt in (0.0, 0.002, 0.01) for xm in (0.0, 0.15) for cap in (0.25, 1.0)
                for l2 in np.round(np.linspace(-0.02, 0.04, 121), 6)]
        S["c234"] = pool.map(c234, args, chunksize=4); print("c234", time.time() - t0, flush=True)
        mc = {}
        for nm, (xm, cap) in (("equity-style", (0.15, 0.25)), ("fixed-income-style", (0.15, 0.25))):
            chunks = [(nm, xm, cap, list(range(k, 20000, 90))) for k in range(90)]
            mc[nm] = dict(xm=xm, cap=cap, draws=[r for ch in pool.map(mc_chunk, chunks) for r in ch])
        S["mc"] = mc; print("mc", time.time() - t0, flush=True)
        S["c5_draws"] = pool.map(c5_draw, range(200))
        S["c5_sweep"] = pool.map(c5_sweep, [(nm, float(l)) for nm in NAMED for l in np.round(np.linspace(-0.01, 0.04, 51), 6)]); print("c5", time.time() - t0, flush=True)
        args6 = [(nm, "etf_rate", r, rx) for nm in NAMED for r in (0, 1e-4, 2e-4, 5e-4, 1e-3, 2.5e-3, 5e-3) for rx in (False, True)]
        args6 += [(nm, "budget", h, rx) for nm in NAMED for h in (1.5, 1.2, 1.0, 0.8, 0.6, 0.4, 0.3, 0.2) for rx in (False, True)]
        S["c6"] = pool.map(c6, args6); print("c6", time.time() - t0, flush=True)
    S["seconds"] = time.time() - t0
    json.dump(rounded(S), open(HERE / "summary.json", "w"), separators=(",", ":"), default=lambda o: o.tolist() if hasattr(o, "tolist") else str(o))
    print("done", S["seconds"])


if __name__ == "__main__":
    main()
