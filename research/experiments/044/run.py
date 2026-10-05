"""Experiment 044: claim 109 (fund decision and two-stage exactness with ETFs at zero, ETF costs, fees and a funded budget;
Statement at 2470ee26) against an exact joint solver. Registered design: experiments/044-claim109-costs-budget-check.md.
Run: uv run python experiments/044/run.py

Coordinates are instruments (x^A funds, x^E ETFs), B^E = I (so Q = (B^A)', columns r_i), Sigma_E = 0. The objective is
Q(x) = alpha~' x^A - (gamma/2) x^A' V x^A + mu_E' w - (gamma/2) w' Sigma_EE w - C(x - x^-), w = x^E + Q x^A, over the fund
box, x^E >= 0 and the funded budget k(x) = h^- - 1'(x - x^-) - C(x - x^-) >= 0.
"""
import json
import multiprocessing as mp
import time
from pathlib import Path

import cvxpy as cp
import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
GAMMA, SCALE = 5.0, 1e4
SF = np.diag([0.08 ** 2, 0.04 ** 2])
BA3 = np.array([[1.0, 0.5], [1.0, 0.2], [1.0, -0.3]])
HT = 1e-7                                          # status tolerance on holdings
OPT = dict(tol_gap_abs=1e-12, tol_gap_rel=1e-10, tol_feas=1e-10, max_iter=500)


class Inst:
    def __init__(self, BA, at, v, kp, km, xm, cap, mu, S, kEp, kEm, xEm, h):
        self.BA = np.atleast_2d(BA); self.N = self.BA.shape[0]; self.Q = self.BA.T; self.M = 2
        self.at, self.v, self.kp, self.km, self.xm, self.cap = map(lambda a: np.asarray(a, float), (at, v, kp, km, xm, cap))
        self.mu, self.S = np.asarray(mu, float), S
        self.kEp, self.kEm, self.xEm, self.h = np.asarray(kEp, float), np.asarray(kEm, float), np.asarray(xEm, float), h

    def cost(self, xA, xE):
        uA, uE = xA - self.xm, xE - self.xEm
        return float(self.kp @ np.maximum(uA, 0) + self.km @ np.maximum(-uA, 0) + self.kEp @ np.maximum(uE, 0) + self.kEm @ np.maximum(-uE, 0))

    def k(self, xA, xE):
        return float(self.h - np.sum(xA - self.xm) - np.sum(xE - self.xEm) - self.cost(xA, xE)) if self.h is not None else np.inf

    def GE(self, w):
        return float(self.mu @ w - 0.5 * GAMMA * w @ self.S @ w)

    def Qv(self, xA, xE):
        w = xE + self.Q @ xA
        return float(self.at @ xA - 0.5 * GAMMA * np.sum(self.v * xA ** 2) + self.GE(w) - self.cost(xA, xE))

    def solve(self, mode="joint", wfix=None, tilt=None, fundsfixed=False, solver="CLARABEL", budget=True):
        """mode joint: the joint problem; fibre: x^E + Q x^A = wfix (dual returned); tilt: G_E replaced by
        -(gamma/2)(w - tilt)' S (w - tilt). fundsfixed: x^A = x^{A-}."""
        N = self.N
        xA, xE = cp.Variable(N), cp.Variable(2, nonneg=True)
        ap, am, ep, em = (cp.Variable(N, nonneg=True), cp.Variable(N, nonneg=True), cp.Variable(2, nonneg=True), cp.Variable(2, nonneg=True))
        C = self.kp @ ap + self.km @ am + self.kEp @ ep + self.kEm @ em
        w = xE + self.Q @ xA
        cons = [xA - self.xm == ap - am, xE - self.xEm == ep - em, xA >= 0, xA <= self.cap]
        if fundsfixed:
            cons += [xA == self.xm]
        bud = None
        if budget and self.h is not None:
            bud = self.h - cp.sum(xA - self.xm) - cp.sum(xE - self.xEm) - C >= 0; cons.append(bud)
        eq = None
        if mode == "fibre":
            eq = w == wfix; cons.append(eq)
        if tilt is None:
            gE = self.mu @ w - 0.5 * GAMMA * cp.quad_form(w, cp.psd_wrap(self.S))
        else:
            gE = -0.5 * GAMMA * cp.quad_form(w - tilt, cp.psd_wrap(self.S))
        obj = self.at @ xA - 0.5 * GAMMA * cp.sum(cp.multiply(self.v, cp.square(xA))) + gE - C
        pr = cp.Problem(cp.Maximize(SCALE * obj), cons)
        if solver == "CLARABEL":
            pr.solve(solver="CLARABEL", **OPT)
        else:
            pr.solve(solver="OSQP", eps_abs=1e-10, eps_rel=1e-10, max_iter=400000, polish=True)
        if pr.status not in ("optimal", "optimal_inaccurate"):
            return None
        out = dict(xA=np.array(xA.value), xE=np.maximum(np.array(xE.value), 0.0), status=pr.status,
                   eta=float(bud.dual_value) / SCALE if bud is not None else 0.0)
        if eq is not None:
            out["s"] = np.array(eq.dual_value) / SCALE
        return out

    def stage1(self):
        """Claim 041's stage 1 over W_F (fees in mu_E; no rates, residuals or budget)."""
        w, x = cp.Variable(2), cp.Variable(self.N)
        cp.Problem(cp.Maximize(SCALE * (self.mu @ w - 0.5 * GAMMA * cp.quad_form(w, cp.psd_wrap(self.S)))),
                   [w >= self.Q @ x, x >= 0, x <= self.cap]).solve(solver="CLARABEL", **OPT)
        return np.array(w.value)


def gen(kind, idx, seed0=2044):
    rng = np.random.default_rng([seed0, 0 if kind == "multi" else 1, idx])
    if kind == "multi":
        BA = BA3; N = 3; cap = rng.choice([0.25, 1.0], 3)
    else:
        BA = np.array([[1.0, 0.5]]) if rng.random() < 0.5 else np.array([[1.0, -0.3]]); N = 1; cap = rng.choice([0.25, 2.0], 1)
    ah = rng.uniform(-0.01, 0.01, N); v = 0.02 ** 2 * (1 + rng.uniform(0.01, 3, N))
    kp, km = rng.uniform(0, 0.02, N), rng.uniform(0, 0.02, N); xm = rng.uniform(0, 1, N) * cap
    lam = rng.uniform(-0.01, 0.03, 2); sds = rng.uniform(0.001, 0.01, 2)
    kEp, kEm = rng.uniform(0, 0.005, 2), rng.uniform(0, 0.005, 2); cE = rng.uniform(0, 0.002, 2)
    xEm = np.where(rng.random(2) < 0.5, 0.0, rng.uniform(0, 0.5, 2))
    hfac = rng.uniform(0.3, 1.5)
    Q = BA.T; mu = lam - cE; at = ah + Q.T @ cE; S = SF + np.diag(sds ** 2)
    I = Inst(BA, at, v, kp, km, xm, cap, mu, S, kEp, kEm, xEm, None)
    free = I.solve()
    need = float(np.sum(free["xA"] - xm) + np.sum(free["xE"] - xEm) + I.cost(free["xA"], free["xE"]))
    I.h = max(need * hfac, 1e-3); I.need = need
    return I


def statuses(I, xE):
    st = []
    for j in range(2):
        if xE[j] <= HT:
            st.append("Z")
        elif xE[j] > I.xEm[j] + HT:
            st.append("B")
        elif xE[j] < I.xEm[j] - HT:
            st.append("S")
        else:
            st.append("I")
    return st


def fund_line(I, g, xA, eta):
    """Residual of g_i = eta + (1 + eta) t_i, t_i in T_i, with box signs; returns the largest violation."""
    viol = 0.0
    for i in range(I.N):
        up, dn = eta + (1 + eta) * I.kp[i], eta - (1 + eta) * I.km[i]
        u = xA[i] - I.xm[i]; at0, atc = xA[i] <= 1e-7, xA[i] >= I.cap[i] - 1e-7
        if u > 1e-7:
            e = max(0.0, up - g[i]) if atc else abs(g[i] - up)
        elif u < -1e-7:
            e = max(0.0, g[i] - dn) if at0 else abs(g[i] - dn)
        else:
            e = max(0.0 if atc else g[i] - up, 0.0 if at0 else dn - g[i], 0.0)
        viol = max(viol, e)
    return viol


def part2(I, x, eta):
    """Claim 109 part 2 at the solver's optimum; returns the formula errors."""
    xA, xE = x["xA"], x["xE"]; w = xE + I.Q @ xA
    gE = I.mu - GAMMA * I.S @ w
    g = I.at - GAMMA * I.v * xA + I.Q.T @ gE
    st = statuses(I, xE)
    T = [j for j in range(2) if st[j] in "BS"]; F = [j for j in range(2) if st[j] in "ZI"]
    t = np.array([I.kEp[j] if st[j] == "B" else (-I.kEm[j] if st[j] == "S" else (I.kEp[j] if I.xEm[j] == 0 else -I.kEm[j])) for j in range(2)])
    pi = eta + (1 + eta) * t
    S, mu = I.S, I.mu
    out = dict(st="".join(st), eta=eta)
    if T:
        STT, STF = S[np.ix_(T, T)], S[np.ix_(T, F)]
        wT = np.linalg.solve(STT, (mu[T] - pi[T]) / GAMMA - STF @ w[F]) if F else np.linalg.solve(STT, (mu[T] - pi[T]) / GAMMA)
        out["e2a"] = float(np.max(np.abs(wT - w[T])))
    if F:
        SFF = S[np.ix_(F, F)]
        if T:
            STT, SFT = S[np.ix_(T, T)], S[np.ix_(F, T)]
            muFT = mu[F] - SFT @ np.linalg.solve(STT, mu[T]); SFFT = SFF - SFT @ np.linalg.solve(STT, SFT.T)
            gF = muFT + SFT @ np.linalg.solve(STT, pi[T]) - GAMMA * SFFT @ w[F]
        else:
            muFT, SFFT = mu[F], SFF
            gF = muFT - GAMMA * SFFT @ w[F]
        out["e2b"] = float(np.max(np.abs(gF - gE[F])))
        zeta = [pi[j] - gE[j] for j in F if st[j] == "Z"]
        out["zeta_min"] = float(min(zeta)) if zeta else None
        idle = [(gE[j] - (eta - (1 + eta) * I.kEm[j]), (eta + (1 + eta) * I.kEp[j]) - gE[j]) for j in F if st[j] == "I"]
        out["idle_min"] = float(min(min(a) for a in idle)) if idle else None
    # 2c
    rF = I.Q[F, :] if F else np.zeros((0, I.N)); rT = I.Q[T, :] if T else np.zeros((0, I.N))
    if F and T:
        rho = rT + np.linalg.solve(S[np.ix_(T, T)], S[np.ix_(T, F)] @ rF)
    else:
        rho = rT
    xF = xE[F] if F else np.zeros(0)
    if F:
        VFT = np.diag(I.v) + rF.T @ SFFT @ rF
        aFT = I.at + rF.T @ muFT - GAMMA * rF.T @ SFFT @ xF + (rho.T @ pi[T] if T else 0)
    else:
        VFT = np.diag(I.v); aFT = I.at + (rho.T @ pi[T] if T else 0)
    G = aFT - GAMMA * VFT @ xA
    out["e2c"] = float(np.max(np.abs(G - g)))
    out["line"] = fund_line(I, g, xA, eta)
    out["line_G"] = fund_line(I, G, xA, eta)
    # 2d, ETFs starting at zero
    d = []
    for j in range(2):
        if I.xEm[j] == 0:
            th = eta + (1 + eta) * I.kEp[j]
            d.append(dict(st=st[j], g=float(gE[j]), th=float(th), gown=float(gE[j] + GAMMA * S[j, j] * xE[j])))
    out["d"] = d
    out["g"] = g.tolist(); out["gE"] = gE.tolist()
    return out


def crit4a(I, x2A, x2E, zeta, k2):
    """4a's criterion at x_2 as a linear feasibility problem in (eta, s): minimize the largest violation tau."""
    N = I.N; nv = 1 + N + 2 + 1                        # eta, s_funds, s_etfs, tau
    A_ub, b_ub, A_eq, b_eq = [], [], [], []
    E = lambda: np.zeros(nv)
    it, ie, iT = 0, 1, 1 + N + 2                          # indices
    G = I.at - GAMMA * I.v * x2A - I.Q.T @ zeta
    def eq_tol(row, rhs):                              # |row . z - rhs| <= tau
        r1 = row.copy(); r1[iT] = -1; A_ub.append(r1); b_ub.append(rhs)
        r2 = -row.copy(); r2[iT] = -1; A_ub.append(r2); b_ub.append(-rhs)
    def le_tol(row, rhs):                              # row . z <= rhs + tau
        r = row.copy(); r[iT] = -1; A_ub.append(r); b_ub.append(rhs)
    def slope_set(idx, u, kp, km):                     # s in (1 + eta) T
        if u > 1e-7:
            r = E(); r[idx] = 1; r[it] = -kp; eq_tol(r, kp)
        elif u < -1e-7:
            r = E(); r[idx] = 1; r[it] = km; eq_tol(r, -km)
        else:
            r = E(); r[idx] = 1; r[it] = -kp; le_tol(r, kp)
            r = E(); r[idx] = -1; r[it] = -km; le_tol(r, km)
    for i in range(N):
        si = ie + i; u = x2A[i] - I.xm[i]
        slope_set(si, u, I.kp[i], I.km[i])
        row = E(); row[it] = 1; row[si] = 1           # eta + s_i  vs  G_i
        at0, atc = x2A[i] <= 1e-7, x2A[i] >= I.cap[i] - 1e-7
        if at0 and not atc:
            le_tol(-row, -G[i])                        # G_i <= eta + s_i
        elif atc and not at0:
            le_tol(row, G[i])                          # G_i >= eta + s_i
        else:
            eq_tol(row, G[i])
    for j in range(2):
        sj = ie + N + j; u = x2E[j] - I.xEm[j]
        slope_set(sj, u, I.kEp[j], I.kEm[j])
        row = E(); row[it] = 1; row[sj] = 1
        if x2E[j] <= 1e-7:
            le_tol(-row, zeta[j])                      # -zeta_j <= eta + s_j
        else:
            eq_tol(row, -zeta[j])
    bounds = [(0, 0 if k2 > 1e-9 else None)] + [(None, None)] * (N + 2) + [(0, None)]
    c = E(); c[iT] = 1
    res = linprog(c, A_ub=np.array(A_ub), b_ub=np.array(b_ub), bounds=bounds, method="highs")
    return float(res.fun) if res.status == 0 else np.inf


def etf_moves(I, x2E):
    out = []
    for j in range(2):
        a, b = I.xEm[j], x2E[j]
        if b <= HT:
            out.append("zero" if a == 0 else "sold_to_zero")
        elif b > a + HT:
            out.append("bought_interior")
        elif b < a - HT:
            out.append("sold_interior")
        else:
            out.append("untraded_interior")
    return out


def draw(args):
    kind, idx = args
    I = gen(kind, idx)
    J1 = I.solve(); J2 = I.solve(solver="OSQP")
    xA, xE = J1["xA"], J1["xE"]; J = I.Qv(xA, xE)
    dis = abs(J - I.Qv(J2["xA"], J2["xE"])) if J2 else None
    dx = float(max(np.max(np.abs(J2["xA"] - xA)), np.max(np.abs(J2["xE"] - xE)))) if J2 else None
    eta = max(J1["eta"], 0.0); kJ = I.k(xA, xE)
    rec = dict(kind=kind, idx=idx, J=J, dis=dis, dx=dx, eta=eta, k=kJ, binding=bool(kJ < 1e-7 and eta > 1e-7), need=I.need, h=I.h)
    rec["p2"] = part2(I, J1, eta)
    wJ = xE + I.Q @ xA
    # knife edges: holdings near status boundaries, marginals near thresholds, budget near binding with small eta
    near = []
    for j in range(2):
        near += [abs(xE[j])] if xE[j] > HT else []
        near += [abs(xE[j] - I.xEm[j])] if abs(xE[j] - I.xEm[j]) > HT else []
    for i in range(I.N):
        for b in (xA[i], I.cap[i] - xA[i], xA[i] - I.xm[i]):
            if abs(b) > HT:
                near.append(abs(b))
    rec["edge"] = bool(min(near + [1.0]) < 1e-6 or (kJ < 1e-7 and eta < 1e-7))
    # part 4: fibre-confined
    ws = I.stage1(); zeta = GAMMA * I.S @ ws - I.mu
    F2 = I.solve("fibre", wfix=ws)
    if F2 is None:
        rec["fibre"] = None
    else:
        x2A, x2E = F2["xA"], F2["xE"]
        exact = bool(max(np.max(np.abs(x2A - xA)), np.max(np.abs(x2E - xE))) <= 1e-5)
        k2 = I.k(x2A, x2E)
        tau = crit4a(I, x2A, x2E, zeta, k2)
        mv = etf_moves(I, x2E)
        coincid = [abs((1 + F2["eta"]) * I.kEm[j] - F2["eta"]) for j in range(2) if mv[j] == "sold_interior"]
        rec["fibre"] = dict(exact=exact, Lam=J - I.Qv(x2A, x2E), tau=tau, crit=bool(tau <= 1e-6), moves=mv, k2=k2, eta2=F2["eta"],
                            kEp=I.kEp.tolist(), coincid=coincid, zeta=zeta.tolist(), zeta_min=float(zeta.min()))
    # part 4c: soft procedure, unconstrained stage 1 and R_E = W_F
    wTB = np.linalg.solve(GAMMA * I.S, I.mu)
    S1 = I.solve(tilt=wTB); rec["Lam_s_free"] = J - I.Qv(S1["xA"], S1["xE"])
    S2 = I.solve(tilt=ws)
    if S2 is not None:
        w2 = S2["xE"] + I.Q @ S2["xA"]; Lam_s = J - I.Qv(S2["xA"], S2["xE"])
        Ssoft = lambda a, e: I.Qv(a, e) - I.GE(e + I.Q @ a) - 0.5 * GAMMA * (e + I.Q @ a - ws) @ I.S @ (e + I.Q @ a - ws)
        rec["soft"] = dict(Lam_s=Lam_s, bound=float(zeta @ (w2 - wJ)), exact=bool(max(np.max(np.abs(S2["xA"] - xA)), np.max(np.abs(S2["xE"] - xE))) <= 1e-5),
                           joint_solves=bool(Ssoft(xA, xE) >= Ssoft(S2["xA"], S2["xE"]) - ((dis or 0) + 1e-10)), zeta_norm=float(np.abs(zeta).max()))
    return rec


def main():
    t0 = time.time()
    with mp.Pool(8) as pool:
        rows = pool.map(draw, [("multi", i) for i in range(500)] + [("one", i) for i in range(500)], chunksize=4)
    S = dict(rows=rows, seconds=time.time() - t0, statement="claim 109 at 2470ee26 (approved, formalized)")
    json.dump(S, open(HERE / "summary.json", "w"), separators=(",", ":"), default=lambda o: o.tolist() if hasattr(o, "tolist") else float(o))
    print("done", S["seconds"])


if __name__ == "__main__":
    main()
