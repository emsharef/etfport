"""Experiment 040: claim 041 (two-stage with ETFs at zero; parts 1, 2, 3(a); Statement at bde0fc3c) against an exact
joint solver. Registered design: experiments/040-claim041-two-stage-at-zero-check.md.  Run: uv run python experiments/040/run.py
"""
import importlib.util
import json
import multiprocessing as mp
import time
from pathlib import Path

import cvxpy as cp
import numpy as np

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("run029", HERE.parent / "029" / "run.py")
m29 = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(m29)
GAMMA, SCALE = m29.GAMMA, m29.SCALE
SF = np.diag([0.08 ** 2, 0.04 ** 2])
BA3 = np.array([[1.0, 0.5], [1.0, 0.2], [1.0, -0.3]])
HT, TOL = 1e-5, 1e-8
OPT = dict(tol_gap_abs=1e-12, tol_gap_rel=1e-10, tol_feas=1e-10, max_iter=500)


class P:
    """Claim 041's coordinates: w (ETF units), x (funds); B^E = I, fees 0."""

    def __init__(self, BA, alpha, v, kp, km, xm, cap, lam, PLm):
        self.BA = np.atleast_2d(BA); self.N = self.BA.shape[0]
        self.Q = self.BA.T                              # R'(B^A)' with R = I
        self.mu = np.asarray(lam, float); self.S = SF + PLm
        self.alpha, self.v = np.asarray(alpha, float), np.asarray(v, float)
        self.kp, self.km, self.xm, self.cap = map(lambda a: np.asarray(a, float), (kp, km, xm, cap))
        self.lam, self.PLm = lam, PLm

    def GE(self, w):
        return float(self.mu @ w - 0.5 * GAMMA * w @ self.S @ w)

    def H(self, x):
        u = x - self.xm
        return float(self.alpha @ x - 0.5 * GAMMA * np.sum(self.v * x ** 2) - self.kp @ np.maximum(u, 0) - self.km @ np.maximum(-u, 0))

    def _cost(self, x):
        up, um = cp.Variable(self.N, nonneg=True), cp.Variable(self.N, nonneg=True)
        return up, um, [x - self.xm == up - um], self.kp @ up + self.km @ um

    def joint(self):
        w, x = cp.Variable(2), cp.Variable(self.N); up, um, c, cost = self._cost(x)
        obj = self.mu @ w - 0.5 * GAMMA * cp.quad_form(w, cp.psd_wrap(self.S)) + self.alpha @ x - 0.5 * GAMMA * cp.sum(cp.multiply(self.v, cp.square(x))) - cost
        cp.Problem(cp.Maximize(SCALE * obj), c + [w >= self.Q @ x, x >= 0, x <= self.cap]).solve(solver="CLARABEL", **OPT)
        return w.value, x.value

    def stage1(self):
        w, x = cp.Variable(2), cp.Variable(self.N)
        cp.Problem(cp.Maximize(SCALE * (self.mu @ w - 0.5 * GAMMA * cp.quad_form(w, cp.psd_wrap(self.S)))), [w >= self.Q @ x, x >= 0, x <= self.cap]).solve(solver="CLARABEL", **OPT)
        return w.value, x.value

    def stage2(self, ws):
        x = cp.Variable(self.N); up, um, c, cost = self._cost(x)
        obj = self.alpha @ x - 0.5 * GAMMA * cp.sum(cp.multiply(self.v, cp.square(x))) - cost
        cp.Problem(cp.Maximize(SCALE * obj), c + [self.Q @ x <= ws + 1e-10, x >= 0, x <= self.cap]).solve(solver="CLARABEL", **OPT)   # Deviation 1: 1e-10 feasibility margin
        return x.value

    def soft2(self, wt):
        w, x = cp.Variable(2), cp.Variable(self.N); up, um, c, cost = self._cost(x)
        obj = self.alpha @ x - 0.5 * GAMMA * cp.sum(cp.multiply(self.v, cp.square(x))) - cost - 0.5 * GAMMA * cp.quad_form(w - wt, cp.psd_wrap(self.S))
        cp.Problem(cp.Maximize(SCALE * obj), c + [w >= self.Q @ x, x >= 0, x <= self.cap]).solve(solver="CLARABEL", **OPT)
        return w.value, x.value

    def VE(self, q):
        w = cp.Variable(2)
        cp.Problem(cp.Maximize(SCALE * (self.mu @ w - 0.5 * GAMMA * cp.quad_form(w, cp.psd_wrap(self.S)))), [w >= q]).solve(solver="CLARABEL", **OPT)
        return self.GE(w.value)

    def fibre_lp(self, ws):
        out = []
        for sgn in (+1, -1):
            x = cp.Variable(self.N)
            cp.Problem(cp.Maximize(SCALE * sgn * x[0]), [self.Q @ x <= ws + 1e-10, x >= 0, x <= self.cap]).solve(solver="CLARABEL", **OPT)
            out.append(float(x.value[0]))
        return out[1], out[0]

    def inst_J(self):
        """The joint value in instrument coordinates (experiment 029's formulation), as a cross-check."""
        I = m29.Inst(self.BA, np.eye(2), self.alpha, self.v, self.kp, self.km, self.xm, self.cap, lam=np.asarray(self.lam), capE=10.0, h=10.0,
                     xEm=np.zeros(2))
        I.St = self.S; I.bTB = np.linalg.solve(GAMMA * I.St, I.lam)
        I.mu = np.concatenate([I.alpha + I.BA @ I.lam, I.BE @ I.lam - I.cE]); I.Sig = I.B @ I.St @ I.B.T + I.Dres
        xs = [m29.solve(I, "joint", s)[0] for s in m29.SOLVERS]
        return I.Q(xs[0]), abs(I.Q(xs[0]) - I.Q(xs[1])), xs[0]


def band_ok(Pb, x2, zeta, tol=1e-7):
    G = Pb.alpha - GAMMA * Pb.v * x2 - Pb.Q.T @ zeta
    ok, near = True, np.inf
    for i in range(Pb.N):
        u = x2[i] - Pb.xm[i]; at0, atc = x2[i] <= HT, x2[i] >= Pb.cap[i] - HT
        if u > HT:
            ok &= (G[i] >= Pb.kp[i] - tol) if atc else abs(G[i] - Pb.kp[i]) < tol
        elif u < -HT:
            ok &= (G[i] <= -Pb.km[i] + tol) if at0 else abs(G[i] + Pb.km[i]) < tol
        else:
            ok &= (G[i] <= Pb.kp[i] + tol or atc) and (G[i] >= -Pb.km[i] - tol or at0)
            near = min(near, abs(G[i] - Pb.kp[i]) if not atc else np.inf, abs(G[i] + Pb.km[i]) if not at0 else np.inf)
    return bool(ok), float(near), G


def draw(args):
    kind, idx = args
    rng = np.random.default_rng([2040, 0 if kind == "multi" else 1, idx])
    if kind == "multi":
        BA = BA3; N = 3; cap = rng.choice([0.25, 1.0], 3)
    else:
        BA = np.array([[1.0, 0.5]]) if rng.random() < 0.5 else np.array([[1.0, -0.3]]); N = 1; cap = rng.choice([0.25, 2.0], 1)
    alpha = rng.uniform(-0.01, 0.01, N); v = 0.02 ** 2 * (1 + rng.uniform(0.01, 3, N))
    kp, km = rng.uniform(0, 0.02, N), rng.uniform(0, 0.02, N); xm = rng.uniform(0, 1, N) * cap
    lam = rng.uniform(-0.01, 0.03, 2); sds = rng.uniform(0.001, 0.01, 2)
    Pb = P(BA, alpha, v, kp, km, xm, cap, lam, np.diag(sds ** 2))
    wJ, xJ = Pb.joint(); J = Pb.GE(wJ) + Pb.H(xJ)
    Ji, dis, xi = Pb.inst_J()
    J_w = J
    if Ji > J + 1e-9:                                  # Deviation 2: take the better of the two joint solves
        xJ = xi[:N]; wJ = xi[N:] + Pb.Q @ xJ; J = Pb.GE(wJ) + Pb.H(xJ)
    ws, x1 = Pb.stage1(); x2 = Pb.stage2(ws); T = Pb.GE(ws) + Pb.H(x2); Lam = J - T
    zeta = GAMMA * Pb.S @ ws - Pb.mu
    slack_ok = bool(np.all(zeta >= -1e-8) and all(zeta[j] <= 1e-7 for j in range(2) if ws[j] - (Pb.Q @ x2)[j] > 1e-7))
    exact_pred, near, G = band_ok(Pb, x2, zeta)
    tol = dis + TOL
    wsoft, xsoft = Pb.soft2(np.linalg.solve(GAMMA * Pb.S, Pb.mu)); Lam_s = J - (Pb.GE(wsoft) + Pb.H(xsoft))
    zJ = [j for j in range(2) if wJ[j] - (Pb.Q @ xJ)[j] <= HT]; z1 = [j for j in range(2) if ws[j] - (Pb.Q @ x1)[j] <= HT]
    out = dict(kind=kind, idx=idx, J=J, J_w=J_w, J_inst_diff=abs(J_w - Ji), J_inst=Ji, J_switched=bool(Ji > J_w + 1e-9), dis=dis, Lam=Lam, x_gap=float(np.max(np.abs(x2 - xJ))), exact_pred=exact_pred, exact_obs=bool(Lam <= tol), near=near,
               slack_ok=slack_ok, zeta_min=float(zeta.min()), Lam_s=Lam_s, ZJ=zJ, Z1=z1, edge=bool(near < 1e-6 or np.min(np.abs(zeta)) < 1e-6 and np.min(np.abs(zeta)) > 1e-12))
    if N == 1:
        r = Pb.Q[:, 0]
        lo_f = max([0.0] + [ws[j] / r[j] for j in range(2) if r[j] < 0]); hi_f = min([Pb.cap[0]] + [ws[j] / r[j] for j in range(2) if r[j] > 0])
        lo_s, hi_s = Pb.fibre_lp(ws)
        band = float(np.clip(np.clip(Pb.xm[0], (Pb.alpha[0] - Pb.kp[0]) / (GAMMA * Pb.v[0]), (Pb.alpha[0] + Pb.km[0]) / (GAMMA * Pb.v[0])), lo_f, hi_f))
        Phi = lambda x: Pb.H(np.array([x])) + Pb.VE(r * x)
        part1 = Phi(xJ[0]) - Phi(x2[0]); part2 = Pb.VE(r * x2[0]) - Pb.GE(ws)
        upper = any(r[j] > 0 and abs(ws[j] - r[j] * x1[0]) <= 1e-7 for j in range(2)); lower = any(r[j] < 0 and abs(ws[j] - r[j] * x1[0]) <= 1e-7 for j in range(2))
        out.update(r=r.tolist(), lo_f=lo_f, hi_f=hi_f, lo_s=lo_s, hi_s=hi_s, x1=float(x1[0]), x2=float(x2[0]), x2_f=band, xJ=float(xJ[0]),
                   in_int=bool(lo_f - HT <= xJ[0] <= hi_f + HT), part1=part1, part2=part2, upper=upper, lower=lower)
    return out


def part3b(args):
    """Deviation 5: claim 041 part 3(b) (approved Statement d9264c80): the soft procedure with stage 1 restricted to the
    feasible exposures W_F, so w_s = w*."""
    kind, idx = args
    rng = np.random.default_rng([2040, 0 if kind == "multi" else 1, idx])
    if kind == "multi":
        BA = BA3; N = 3; cap = rng.choice([0.25, 1.0], 3)
    else:
        BA = np.array([[1.0, 0.5]]) if rng.random() < 0.5 else np.array([[1.0, -0.3]]); N = 1; cap = rng.choice([0.25, 2.0], 1)
    alpha = rng.uniform(-0.01, 0.01, N); v = 0.02 ** 2 * (1 + rng.uniform(0.01, 3, N))
    kp, km = rng.uniform(0, 0.02, N), rng.uniform(0, 0.02, N); xm = rng.uniform(0, 1, N) * cap
    lam = rng.uniform(-0.01, 0.03, 2); sds = rng.uniform(0.001, 0.01, 2)
    Pb = P(BA, alpha, v, kp, km, xm, cap, lam, np.diag(sds ** 2))
    wJ, xJ = Pb.joint(); J = Pb.GE(wJ) + Pb.H(xJ)
    Ji, dis, xi = Pb.inst_J()
    if Ji > J + 1e-9:
        xJ = xi[:N]; wJ = xi[N:] + Pb.Q @ xJ; J = Pb.GE(wJ) + Pb.H(xJ)
    ws, _ = Pb.stage1()
    w2, xs = Pb.soft2(ws); Lam_s = J - (Pb.GE(w2) + Pb.H(xs))
    wTB = np.linalg.solve(GAMMA * Pb.S, Pb.mu)
    x = cp.Variable(N); pr = cp.Problem(cp.Minimize(0), [Pb.Q @ x <= wTB, x >= 0, x <= Pb.cap]); pr.solve(solver="CLARABEL")
    reach = pr.status in ("optimal", "optimal_inaccurate")
    nu = Pb.mu - GAMMA * Pb.S @ ws
    # nu in the normal cone of W_F at w*: nu <= 0 and max over the box of nu' Q x <= nu' w*
    xv = cp.Variable(N); pv = cp.Problem(cp.Maximize(SCALE * (nu @ (Pb.Q @ xv))), [xv >= 0, xv <= Pb.cap]); pv.solve(solver="CLARABEL")
    cone = bool(np.all(nu <= 1e-9) and nu @ (Pb.Q @ xv.value) <= nu @ ws + 1e-9)
    # the tilted stage 2 at the joint optimum: does the joint optimum attain the soft stage 2's value?
    S = lambda w_, x_: Pb.H(x_) - 0.5 * GAMMA * (w_ - ws) @ Pb.S @ (w_ - ws)
    TOL3 = 1e-10                                            # Deviation 5: the tilted-stage-2 test at the objective resolution
    joint_solves = bool(S(wJ, xJ) >= S(w2, xs) - (dis + TOL3)); gapS = float(S(w2, xs) - S(wJ, xJ))
    return dict(kind=kind, idx=idx, reach=reach, Lam_s=Lam_s, bound=float(nu @ (wJ - w2)), nu_norm=float(np.abs(nu).max()), cone=cone,
                joint_solves=joint_solves, exact_loss=bool(Lam_s <= dis + TOL3), gapS=gapS, dis=dis,
                x_gap=float(np.max(np.abs(xs - xJ))), w_gap=float(np.max(np.abs(w2 - wJ))),
                exact=bool(max(np.max(np.abs(xs - xJ)), np.max(np.abs(w2 - wJ))) <= 1e-4))   # Deviation 5: exact on the solution (x, w)


def main3b():
    S = json.load(open(HERE / "summary.json"))
    with mp.Pool(9) as pool:
        S["part3b"] = pool.map(part3b, [("multi", i) for i in range(500)] + [("one", i) for i in range(500)], chunksize=4)
    S["part3b_statement"] = "claim 041 approved at d9264c80 (3(b) as in bde0fc3c)"
    json.dump(S, open(HERE / "summary.json", "w"), separators=(",", ":"), default=lambda o: o.tolist() if hasattr(o, "tolist") else float(o))
    print("3b done")


def main():
    t0 = time.time()
    with mp.Pool(9) as pool:
        S = dict(rows=pool.map(draw, [("multi", i) for i in range(500)] + [("one", i) for i in range(500)], chunksize=4))
    S["seconds"] = time.time() - t0; S["statement"] = "claim 041 at math/claim041-two-stage-etfs-at-zero bde0fc3c"
    json.dump(S, open(HERE / "summary.json", "w"), separators=(",", ":"), default=lambda o: o.tolist() if hasattr(o, "tolist") else float(o))
    print("done", S["seconds"])


if __name__ == "__main__":
    import sys as _sys
    main3b() if _sys.argv[1:] == ["3b"] else main()
