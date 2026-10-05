"""Finite checks for claim 027 (D4: the two-stage factor-then-manager procedure in M2); not its proof.

Run: uv run python checks/027/check.py

On experiment 006's calibrated M2 cells (French factor means and shock sizes, assumed alpha,
residuals, drag, costs; geometries G1-exact, G2-missing, G3-infeasible; costs Z and EQ5;
gamma = 5; start S1), the check solves (floating CLARABEL, not certificates):
- the joint optimum J = max_F Qbar;
- stage 1: the feasibility-aware factor target b* maximizing G(b) = b'lambda - (gamma/2) b'Sigma_f b
  over the funded feasible exposure set b(F); and the unconstrained Treynor-Black target
  b_TB = Sigma_f^{-1} lambda / gamma, with whether it lies in b(F);
- stage 2: V(b*) = max {H(w): w in F, b(w) = b*} and the two-stage value T = G(b*) + V(b*);
and verifies the exact decomposition Qbar = G(b) + H, the loss identity
J - T = [V(b_J) - V(b*)] - [G(b*) - G(b_J)], the bound J - T <= V(b_J) - V(b*) - (gamma/2)||b_J - b*||^2_{Sigma_f},
nonnegativity, exact separation (zero loss) in a Treynor-Black cell (costless, drag-free,
residual-free spanning ETFs with slack funding), and positive loss in the missing-direction geometry
with nonzero alpha.
"""
import itertools
import math
import sys

import cvxpy as cp
import numpy as np

LAM = np.array([0.0184, 0.00897])
SIZES = np.array([0.0854, 0.0610])
SIG_F = np.diag(SIZES ** 2)
BA = np.array([1.0, 0.3])
GEOS = {"G1-exact": [np.array([1.0, 0.0]), np.array([1.0, 0.3])],
        "G2-missing": [np.array([1.0, 0.0])],
        "G3-infeasible": [np.array([1.0, 0.0]), np.array([1.0, 0.15])],
        "pure-factor": [np.array([1.0, 0.0]), np.array([0.0, 1.0])]}
COSTS = {"Z": 0.0, "EQ5": 0.0005}


class Cell:
    def __init__(self, geo, cost, alpha, gamma=5.0, resA=0.01, resE=0.002, drag=1e-4, tb=False):
        self.BE = GEOS[geo]; n = len(self.BE)
        self.B = np.vstack([BA] + self.BE)                 # rows: instruments, cols: factors
        self.alpha, self.gamma = alpha, gamma
        self.drag = np.zeros(n) if tb else np.full(n, drag)
        self.kappa = 0.0 if tb else cost
        self.kappaA = cost
        # residual variances (independent shocks): active resA, ETFs resE (0 in the Treynor-Black cell)
        self.res = np.array([resA ** 2] + [0.0 if tb else resE ** 2] * n)
        self.Sigma = self.B @ SIG_F @ self.B.T + np.diag(self.res)
        self.x0 = np.array([0.5, 0.4] + [0.0] * (n - 1)); self.h0 = 0.1
        self.cap = np.ones(1 + n)
        self.tb = tb

    def fees(self, w):
        u = w - self.x0
        rates_b = np.array([self.kappaA] + [self.kappa] * len(self.BE)); rates_s = rates_b
        return rates_b @ cp.pos(u) + rates_s @ cp.pos(-u)

    def feasible(self, w):
        return [w >= 0, w <= self.cap, self.h0 - cp.sum(w - self.x0) - self.fees(w) >= 0]

    def b(self, w):
        return self.B.T @ w

    def G(self, b):
        return b @ LAM - self.gamma / 2 * b @ SIG_F @ b

    def Hexpr(self, w):
        mu_res = np.array([self.alpha] + list(-self.drag))
        return mu_res @ w - self.gamma / 2 * cp.sum(cp.multiply(self.res, cp.square(w))) - self.fees(w)

    def Qexpr(self, w):
        b = self.b(w)
        return b @ LAM - self.gamma / 2 * cp.quad_form(b, SIG_F) + self.Hexpr(w)

    def solve(self, obj, extra=()):
        w = cp.Variable(1 + len(self.BE))
        prob = cp.Problem(cp.Maximize(obj(w)), self.feasible(w) + list(extra(w) if callable(extra) else extra))
        prob.solve(solver="CLARABEL")
        assert prob.status in ("optimal", "optimal_inaccurate"), prob.status
        return prob.value, np.array(w.value)

    def two_stage(self):
        J, wJ = self.solve(self.Qexpr)
        bJ = self.b(wJ)
        Gstar, w1 = self.solve(lambda w: self.b(w) @ LAM - self.gamma / 2 * cp.quad_form(self.b(w), SIG_F))
        bstar = self.b(w1)
        V, w2 = self.solve(self.Hexpr, lambda w: [cp.abs(self.b(w) - bstar) <= 1e-9])
        VJ, _ = self.solve(self.Hexpr, lambda w: [cp.abs(self.b(w) - bJ) <= 1e-9])
        T = self.G(bstar) + V
        b_tb = np.linalg.solve(SIG_F, LAM) / self.gamma
        # feasibility of the unconstrained target: is there w in F with b(w) = b_tb?
        try:
            self.solve(lambda w: 0 * cp.sum(w), lambda w: [cp.abs(self.b(w) - b_tb) <= 1e-9]); tb_feasible = True
        except AssertionError:
            tb_feasible = False
        return dict(J=J, T=T, loss=J - T, bJ=bJ, bstar=bstar, VJ=VJ, V=V, Gstar=self.G(bstar), GJ=self.G(bJ),
                    b_tb=b_tb, tb_feasible=tb_feasible, wJ=wJ, w2=w2)


def main():
    TOL = 2e-6
    rows = []
    for geo, cost, alpha in itertools.product(["G1-exact", "G2-missing", "G3-infeasible"], COSTS, [-0.005, -0.0025, 0.0, 0.0025, 0.005]):
        c = Cell(geo, COSTS[cost], alpha)
        r = c.two_stage()
        # identity and bound
        ident = (r["VJ"] - r["V"]) - (r["Gstar"] - r["GJ"])
        assert abs(r["loss"] - ident) < TOL, (geo, cost, alpha, r["loss"], ident)
        d = r["bJ"] - r["bstar"]
        bound = (r["VJ"] - r["V"]) - c.gamma / 2 * d @ SIG_F @ d
        assert r["loss"] >= -TOL and r["loss"] <= bound + TOL, (geo, cost, alpha, r["loss"], bound)
        assert r["Gstar"] >= r["GJ"] - TOL
        rows.append((geo, cost, alpha, r))
        print(f"  {geo:14s} {cost:4s} alpha {alpha * 1e4:+5.0f} bp: joint {r['J'] * 1e4:8.3f} bp, two-stage {r['T'] * 1e4:8.3f} bp, "
              f"loss {r['loss'] * 1e4:7.3f} bp, mismatch ||b_J-b*||_Sigma_f {math.sqrt(max(d @ SIG_F @ d, 0)):.4f}, "
              f"TB target {'feasible' if r['tb_feasible'] else 'infeasible'}")
    # Exact-separation cell: pure-factor ETFs, costless, drag-free, residual-free, slack funding, gamma = 20 so the
    # unconstrained target b_TB = Sigma_f^{-1} lambda/gamma is feasible, and alpha = 1 bp so the residual-optimal
    # active holding alpha/(gamma sigma_A^2) = 0.05 lies inside the exposure fibre: V is flat at b* and the loss is 0.
    tbc = Cell("pure-factor", 0.0, 0.0001, gamma=20.0, tb=True)
    tbc.x0 = np.array([0.05, 0.05, 0.05]); tbc.h0 = 0.85
    r = tbc.two_stage()
    assert abs(r["loss"]) < 1e-6 and r["tb_feasible"], (r["loss"], r["tb_feasible"])
    print(f"  exact-separation cell (pure-factor costless residual-free ETFs, slack funding, small alpha): loss {r['loss'] * 1e4:.5f} bp; "
          f"TB target feasible; b* = {np.round(r['bstar'], 4)}, b_TB = {np.round(r['b_tb'], 4)}")
    # the same cell with alpha = 25 bp: the residual optimum 1.25 exceeds the fibre's bound b*_1, so V is not flat
    tbc2 = Cell("pure-factor", 0.0, 0.0025, gamma=20.0, tb=True)
    tbc2.x0 = np.array([0.05, 0.05, 0.05]); tbc2.h0 = 0.85
    r2 = tbc2.two_stage()
    assert r2["loss"] > 1e-5, r2["loss"]
    print(f"  same cell with alpha = 25 bp: the exposure target binds the active holding; loss {r2['loss'] * 1e4:.3f} bp")
    # missing direction with nonzero alpha: positive loss
    miss = [r for g, cst, a, r in rows if g == "G2-missing" and a != 0.0]
    assert all(r["loss"] > 1e-6 for r in miss), [r["loss"] for r in miss]
    print(f"  G2-missing with alpha != 0: loss positive in all {len(miss)} cells (min {min(r['loss'] for r in miss) * 1e4:.3f} bp)")
    print("checks/027: all checks passed")


if __name__ == "__main__":
    main()
    sys.exit(0)
