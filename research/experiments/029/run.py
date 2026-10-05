"""Experiment 029: claim 104 (two-stage exactness and loss, one review, M7) against an independent one-review solver.
Registered design: experiments/029-criterion-c-check.md.  Run: uv run python experiments/029/run.py

My own formulation of claim 104's Setting (no code shared with checks/104): directional proportional rates,
caps 0 <= x <= bar x, funded cash 1'(x - x^-) + C(x - x^-) <= h^-; the joint problem, the fibre-confined two-stage
procedure (claim 027) and the soft procedure (claim 028); every program solved with CLARABEL and with OSQP.
The shared one-review solver (`Inst`, `solve`) is reused by experiments 030, 032 and 034.
"""
import itertools
import json
import multiprocessing as mp
import time
from pathlib import Path

import cvxpy as cp
import numpy as np

HERE = Path(__file__).resolve().parent
GAMMA = 5.0
SF = np.diag([0.08 ** 2, 0.04 ** 2])
PL = np.diag([0.005 ** 2, 0.005 ** 2])
LAM = np.array([0.015, 0.005])
BA3 = np.array([[1.0, 0.5], [1.0, 0.2], [1.0, -0.3]])
BE_SPAN = np.eye(2)                         # Deviation 1: the registered [[1, 0], [0.9, 0.4]] puts the ETF incumbents at (-1.13, 1.44)
V = 0.02 ** 2 + 0.0035 ** 2
SOLVERS = ("CLARABEL", "OSQP")
ZERO_TRADE, BAND_SLACK = 1e-7, 1e-8
SCALE = 1e4                                 # Deviation 2: objectives solved in bp units for position accuracy
INTERIOR = 1e-5                             # Deviation 2: "strictly inside its box" means at least 1e-5 from each bound


class Inst:
    """One review of an M7 instance in M5's reference case (claim 104's Setting). Instruments: funds then ETFs."""

    def __init__(self, BA, BE, alpha, v, kp, km, xm, cap, lam=LAM, cE=None, SigE=None, kEp=None, kEm=None, capE=1.0,
                 xEm=None, h=1.0):
        self.BA, self.BE = np.atleast_2d(BA), np.atleast_2d(BE)
        self.N, self.M = self.BA.shape[0], self.BE.shape[0]
        self.n = self.N + self.M
        self.B = np.vstack([self.BA, self.BE])
        self.St = SF + PL                     # Sigma~_f
        self.lam = np.asarray(lam, float)
        self.alpha = np.broadcast_to(np.asarray(alpha, float), (self.N,)).copy()
        self.v = np.broadcast_to(np.asarray(v, float), (self.N,)).copy()
        self.cE = np.zeros(self.M) if cE is None else np.broadcast_to(np.asarray(cE, float), (self.M,)).copy()
        self.SigE = np.zeros((self.M, self.M)) if SigE is None else np.asarray(SigE, float)
        z = np.zeros(self.M)
        self.kp = np.concatenate([np.broadcast_to(kp, (self.N,)), z if kEp is None else np.broadcast_to(kEp, (self.M,))]).astype(float)
        self.km = np.concatenate([np.broadcast_to(km, (self.N,)), z if kEm is None else np.broadcast_to(kEm, (self.M,))]).astype(float)
        xAm = np.broadcast_to(np.asarray(xm, float), (self.N,)).copy()
        self.bTB = np.linalg.solve(GAMMA * self.St, self.lam)
        if xEm is None:                        # ETFs at the Markowitz exposure's remainder, clipped to the box
            xEm = np.clip(np.linalg.lstsq(self.BE.T, self.bTB - self.BA.T @ xAm, rcond=None)[0], 0.0, capE)
        self.xm = np.concatenate([xAm, np.broadcast_to(np.asarray(xEm, float), (self.M,))])
        self.cap = np.concatenate([np.broadcast_to(np.asarray(cap, float), (self.N,)), np.full(self.M, capE)])
        self.h = h
        self.mu = np.concatenate([self.alpha + self.BA @ self.lam, self.BE @ self.lam - self.cE])
        D = np.zeros((self.n, self.n)); D[:self.N, :self.N] = np.diag(self.v); D[self.N:, self.N:] = self.SigE
        self.Sig = self.B @ self.St @ self.B.T + D
        self.Dres = D

    # objective pieces, numpy
    def C(self, x):
        u = x - self.xm; return float(self.kp @ np.maximum(u, 0) + self.km @ np.maximum(-u, 0))

    def Q(self, x):
        return float(self.mu @ x - 0.5 * GAMMA * x @ self.Sig @ x - self.C(x))

    def G(self, b):
        return float(self.lam @ b - 0.5 * GAMMA * b @ self.St @ b)

    def H(self, x):
        return float(self.alpha @ x[:self.N] - self.cE @ x[self.N:] - 0.5 * GAMMA * x @ self.Dres @ x - self.C(x))

    def g(self, x):
        return self.mu - GAMMA * self.Sig @ x

    def cash(self, x):
        return float(self.h - np.sum(x - self.xm) - self.C(x))


def _feasible(I, x, up, um):
    return [x == I.xm + up - um, up >= 0, um >= 0, x >= 0, x <= I.cap,
            cp.sum(up - um) + I.kp @ up + I.km @ um <= I.h]


def solve(I, kind, solver, b_fix=None, box=None, direction=None):
    """kind: 'joint' | 'stage1' | 'stage2' (fibre b_fix) | 'soft1' (G over box R) | 'soft2' (S with b_fix) | 'lp' (extreme of b_k).
    Returns (x or b, eta, status)."""
    n, K = I.n, 2
    opts = dict(CLARABEL=dict(tol_gap_abs=1e-12, tol_gap_rel=1e-10, tol_feas=1e-10, max_iter=500),
                OSQP=dict(eps_abs=1e-10, eps_rel=1e-10, polish=True, max_iter=400000))[solver]
    if kind == "soft1":
        b = cp.Variable(K)
        prob = cp.Problem(cp.Maximize(SCALE * (I.lam @ b - 0.5 * GAMMA * cp.quad_form(b, cp.psd_wrap(I.St)))), [b >= box[0], b <= box[1]])
        prob.solve(solver=solver, **opts); return b.value, None, prob.status
    x, up, um = cp.Variable(n), cp.Variable(n), cp.Variable(n)
    cons = _feasible(I, x, up, um); cost = I.kp @ up + I.km @ um
    b = I.B.T @ x
    if kind == "joint":
        obj = I.mu @ x - 0.5 * GAMMA * cp.quad_form(x, cp.psd_wrap(I.Sig)) - cost
    elif kind == "stage1":
        obj = I.lam @ b - 0.5 * GAMMA * cp.quad_form(b, cp.psd_wrap(I.St))
    else:
        Hx = I.alpha @ x[:I.N] - I.cE @ x[I.N:] - 0.5 * GAMMA * cp.quad_form(x, cp.psd_wrap(I.Dres)) - cost
        if kind == "stage2":
            obj = Hx; cons.append(b == b_fix)
        elif kind == "soft2":
            obj = Hx - 0.5 * GAMMA * cp.quad_form(b - b_fix, cp.psd_wrap(I.St))
        elif kind == "lp":
            obj = direction @ b
    prob = cp.Problem(cp.Maximize(SCALE * obj), cons)
    prob.solve(solver=solver, **opts)
    if kind == "stage1":
        return (I.B.T @ x.value), None, prob.status
    eta = float(cons[-1].dual_value) / SCALE if kind == "joint" and cons[-1].dual_value is not None else None
    if kind == "lp":
        return float(direction @ (I.B.T @ x.value)), None, prob.status
    return x.value, eta, prob.status


def criterion(I, x2, e_tol=BAND_SLACK):
    """Claim 104 part 2b in the inputs, at the stage-2 point: (ETF self-band, fund bands, part-0 test with eta = 0)."""
    def ok(val, i, x):
        u = x[i] - I.xm[i]
        at0, atcap = x[i] <= ZERO_TRADE, x[i] >= I.cap[i] - ZERO_TRADE
        if u > ZERO_TRADE:
            t = [I.kp[i]]
        elif u < -ZERO_TRADE:
            t = [-I.km[i]]
        else:
            t = [-I.km[i], I.kp[i]]
        lo, hi = val - max(t), val - min(t)       # range of val - t over t in T_i
        if at0 and atcap:
            return True
        if at0:
            return lo <= e_tol
        if atcap:
            return hi >= -e_tol
        return lo <= e_tol and hi >= -e_tol
    N = I.N
    etf_marg = -I.cE - GAMMA * I.SigE @ x2[N:]
    fund_marg = I.alpha - GAMMA * I.v * x2[:N]
    self_band = all(ok(etf_marg[j], N + j, x2) for j in range(I.M))
    fund_band = all(ok(fund_marg[i], i, x2) for i in range(N))
    g = I.g(x2)
    part0 = all(ok(g[i], i, x2) for i in range(I.n))
    return self_band, fund_band, part0


def evaluate(I, soft_box=None):
    """Joint, fibre-confined (and soft) solves with both solvers; the primary solver's numbers plus the disagreement."""
    out = {}
    for s in SOLVERS:
        xJ, eta, stJ = solve(I, "joint", s)
        bstar, _, st1 = solve(I, "stage1", s)
        x2, _, st2 = solve(I, "stage2", s, b_fix=bstar)
        r = dict(xJ=xJ, eta=eta, bstar=bstar, x2=x2, J=I.Q(xJ), T=I.Q(x2), status=[stJ, st1, st2])
        r["Lam"] = r["J"] - r["T"]
        if soft_box is not None:
            bs, _, s1 = solve(I, "soft1", s, box=soft_box)
            xs, _, s2 = solve(I, "soft2", s, b_fix=bs)
            r.update(bsoft=bs, xs=xs, Lam_s=r["J"] - I.Q(xs)); r["status"] += [s1, s2]
        out[s] = r
    a, b = out["CLARABEL"], out["OSQP"]
    dis = max(abs(a["J"] - b["J"]), abs(a["T"] - b["T"]), abs(a["Lam"] - b["Lam"]))      # objective units (Deviation 2)
    xdis = max(np.abs(a["xJ"] - b["xJ"]).max(), np.abs(a["x2"] - b["x2"]).max())
    if soft_box is not None:
        dis = max(dis, abs(a["Lam_s"] - b["Lam_s"])); xdis = max(xdis, np.abs(a["xs"] - b["xs"]).max())
    a["disagree"] = float(dis); a["xdisagree"] = float(xdis); a["osqp_status"] = b["status"]
    return a


def bf_box(I):
    lo, hi = np.zeros(2), np.zeros(2)
    for k in range(2):
        d = np.zeros(2); d[k] = 1.0
        hi[k] = solve(I, "lp", "CLARABEL", direction=d)[0]
        lo[k] = -solve(I, "lp", "CLARABEL", direction=-d)[0]
    return lo, hi


def interior(I, x, eta=None):
    """ETFs strictly inside their box and budget slack."""
    xe = x[I.N:]
    return bool(np.all(xe > INTERIOR) and np.all(xe < I.cap[I.N:] - INTERIOR) and I.cash(x) > INTERIOR)


def fl(v):
    return None if v is None else (float(v) if np.ndim(v) == 0 else [float(t) for t in v])


# ---------------------------------------------------------------- curves ----------
def curve1_point(seed_idx):
    rng = np.random.default_rng([2029, 0, seed_idx])
    alpha = rng.uniform(-0.01, 0.01, 3); v = 0.02 ** 2 * (1 + rng.uniform(0.01, 3, 3))
    kp, km = rng.uniform(0, 0.02, 3), rng.uniform(0, 0.02, 3)
    xm = rng.uniform(0, 0.25, 3); cap = rng.choice([0.1, 0.25, 1.0], 3); xm = np.minimum(xm, cap)
    I = Inst(BA3, BE_SPAN, alpha, v, kp, km, xm, cap)
    r = evaluate(I, soft_box=bf_box(I))
    return dict(idx=seed_idx, Lam=r["Lam"], Lam_s=r["Lam_s"], disagree=r["disagree"], xdisagree=r["xdisagree"], hyp=interior(I, r["xJ"]),
                eta=r["eta"], status=r["status"], osqp=r["osqp_status"])


def curve2_point(args):
    rateE, m, sigE = args
    kp = km = 0.001
    alpha = GAMMA * V * 0.1 * np.ones(3); alpha[0] = m + GAMMA * V * 0.1
    SigE = None if sigE == 0 else np.eye(2) * sigE ** 2
    I = Inst(BA3, BE_SPAN, alpha, V, kp, km, 0.1, 0.25, kEp=rateE, kEm=rateE, SigE=SigE)
    r = evaluate(I)
    sb, fb, p0 = criterion(I, r["x2"])
    return dict(rateE=rateE, m=m, sigE=sigE, Lam=r["Lam"], self_band=sb, fund_band=fb, part0=p0,
                bstar_is_bTB=float(np.abs(r["bstar"] - I.bTB).max()), hyp=interior(I, r["x2"]) and interior(I, r["xJ"]),
                x2_1=float(r["x2"][0]), xJ_1=float(r["xJ"][0]), disagree=r["disagree"], xdisagree=r["xdisagree"], status=r["status"], osqp=r["osqp_status"])


def LE_bound(I):
    R = np.linalg.inv(I.BE)
    w, U = np.linalg.eigh(I.St); Sih = U @ np.diag(w ** -0.5) @ U.T
    kmax = np.maximum(I.kp[I.N:], I.km[I.N:])
    return np.linalg.norm(Sih @ R, 2) * (np.linalg.norm(I.cE) + GAMMA * np.linalg.norm(I.SigE, 2) * np.linalg.norm(I.cap[I.N:]) + np.linalg.norm(kmax))


def curve3_point(args):
    name, fee, rateE = args
    a, rate = {"equity-style": (-0.0019, 0.005), "fixed-income-style": (0.0020, 0.002)}[name]
    I = Inst(BA3, BE_SPAN, a, V, rate, rate, 0.1, 0.25, cE=fee, kEp=rateE, kEm=rateE)
    r = evaluate(I)
    L = LE_bound(I); d = r["xJ"] @ I.B - r["bstar"]
    return dict(name=name, fee=fee, rateE=rateE, Lam=r["Lam"], bound=L ** 2 / (2 * GAMMA), LE=L,
                bound2=L * float(np.sqrt(d @ I.St @ d)), hyp=interior(I, r["x2"]), disagree=r["disagree"], xdisagree=r["xdisagree"],
                status=r["status"], osqp=r["osqp_status"])


def reduced_formula(I, i=0):
    """Claim 104 part 2c's reduced moments (hedge map J, Schur complement), from the Statement."""
    Q_, _ = np.linalg.qr(I.BE.T); PiR = Q_ @ Q_.T; PiU = np.eye(2) - PiR
    St = I.St
    SRR, SRU, SUU = PiR @ St @ PiR, PiR @ St @ PiU, PiU @ St @ PiU
    SRRi = np.linalg.pinv(SRR)
    J = PiU - PiR @ SRRi @ SRU
    schur = SUU - SRU.T @ SRRi @ SRU
    bA = I.BA[i]
    ared = I.alpha[i] + bA @ J.T @ I.lam
    sred = I.v[i] + bA @ schur @ bA
    astar = float(np.clip(bA @ J.T @ I.lam / (GAMMA * bA @ schur @ bA), 0, I.cap[i]))
    kp, km, xm = I.kp[i], I.km[i], I.xm[i]
    aJ = float(np.clip(np.clip(xm, (ared - kp) / (GAMMA * sred), (ared + km) / (GAMMA * sred)), 0, I.cap[i]))
    psi = lambda a: ared * a - 0.5 * GAMMA * sred * a ** 2 - kp * max(a - xm, 0) - km * max(xm - a, 0)
    mJ = ared - GAMMA * sred * aJ
    muJ = max(0.0, mJ - kp, -km - mJ)
    d = aJ - astar
    return dict(ared=float(ared), sred=float(sred), astar=astar, aJ=aJ, Lam=psi(aJ) - psi(astar),
                lower=0.5 * GAMMA * sred * d ** 2, upper=0.5 * GAMMA * sred * d ** 2 + (kp + km + muJ) * abs(d), muJ=muJ)


def curve4_point(args):
    a, rate, xm, cap = args
    bTB1 = np.linalg.solve(GAMMA * (SF + PL), LAM)[0]
    I = Inst(BA3[:1], np.array([[1.0, 0.0]]), a, V, rate, rate, xm, cap, xEm=np.clip(bTB1 - xm, 0, 1))
    r = evaluate(I); f = reduced_formula(I)
    hyp = interior(I, r["x2"]) and interior(I, r["xJ"])
    return dict(a=a, rate=rate, xm=xm, cap=cap, Lam=r["Lam"], x2_1=float(r["x2"][0]), xJ_1=float(r["xJ"][0]), hyp=hyp,
                disagree=r["disagree"], xdisagree=r["xdisagree"], status=r["status"], osqp=r["osqp_status"], **{f"f_{k}": v for k, v in f.items()})


def curve5_point(l1):
    I = Inst(BA3, BE_SPAN, GAMMA * V * 0.1, V, 0.002, 0.002, 0.1, 0.25, lam=np.array([l1, LAM[1]]))
    box = bf_box(I)
    r = evaluate(I, soft_box=box)
    nu = I.lam - GAMMA * I.St @ r["bsoft"]
    bJ, bs = I.B.T @ r["xJ"], I.B.T @ r["xs"]
    inR = bool(np.all(I.bTB >= box[0] - 1e-9) and np.all(I.bTB <= box[1] + 1e-9))
    return dict(l1=l1, Lam_s=r["Lam_s"], Lam=r["Lam"], nu=fl(nu), b1=float(nu @ (bJ - bs)), b2=float(nu @ (r["bsoft"] - bs)),
                bTB_in_R=inR, eta=r["eta"], box=[fl(box[0]), fl(box[1])], bTB=fl(I.bTB), disagree=r["disagree"], xdisagree=r["xdisagree"],
                status=r["status"], osqp=r["osqp_status"])


def main():
    t0 = time.time(); S = {}
    with mp.Pool(9) as pool:
        S["c1"] = pool.map(curve1_point, range(200)); print("c1", time.time() - t0, flush=True)
        ms = np.round(np.linspace(-0.008, 0.008, 161), 6)
        args2 = [(re, float(m), 0.0) for re in (0.0, 0.001, 0.005, 0.01) for m in ms] + [(0.005, float(m), 0.001) for m in ms]
        S["c2"] = pool.map(curve2_point, args2); print("c2", time.time() - t0, flush=True)
        args3 = [(nm, f, re) for nm in ("equity-style", "fixed-income-style") for f in (0, 0.00025, 0.0005, 0.001, 0.002, 0.003)
                 for re in (0, 0.0005, 0.001, 0.0025, 0.005, 0.01)]
        S["c3"] = pool.map(curve3_point, args3); print("c3", time.time() - t0, flush=True)
        args4 = [(float(a), rt, xm, cap) for a in np.round(np.linspace(-0.01, 0.01, 201), 6) for rt in (0.0, 0.002, 0.01)
                 for xm in (0.0, 0.15) for cap in (0.25, 1.0)]
        S["c4"] = pool.map(curve4_point, args4); print("c4", time.time() - t0, flush=True)
        S["c5"] = pool.map(curve5_point, [float(v) for v in np.round(np.linspace(0.005, 0.08, 76), 6)]); print("c5", time.time() - t0, flush=True)
    S["seconds"] = time.time() - t0
    json.dump(S, open(HERE / "summary.json", "w"), default=lambda o: o.tolist() if hasattr(o, "tolist") else str(o))
    print("done", S["seconds"])


if __name__ == "__main__":
    main()
