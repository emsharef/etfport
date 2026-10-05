"""Finite checks for claim 028 (D4: the soft-target two-stage procedure in M2); not its proof.

Run: uv run python checks/028/check.py

On experiment 006's calibrated M2 cells (French factor means and shock sizes, assumed alpha, residuals,
drag, costs; geometries G1-exact, G2-missing, G3-infeasible; costs Z and EQ5; gamma = 5; start S1), the
check solves (floating CLARABEL, not certificates):
- the joint optimum J = max_F Qbar and its exposure b_J;
- stage 1: the target b* maximizing G(b) = b'lambda - (gamma/2) b'Sigma_f b over R_0 = {B'w: w >= 0,
  sum w <= 1} (experiment 018's implementable set) and, as a variant, over b(F); the multiplier
  nu = lambda - gamma Sigma_f b*;
- the soft stage 2 (018's 2S-alpha): maximize the residual score with the factor risk charged on the
  distance from b*, over F; its value T_s = Qbar(w_2) and loss J - T_s;
- the fibre-confined stage 2 of claim 027 at the same target, when feasible;
and verifies part 1's identity S = Qbar - nu'b - (gamma/2) b*'Sigma_f b* at random holdings, the
containment nu'(b_J - b*) <= 0, the bounds 0 <= loss <= nu'Delta e <= nu'(b* - b_2), the exact-form
inequality loss <= nu'Delta e - (gamma/2) Delta w'Sigma Delta w, the relation loss_s <= loss_fibre +
nu'(b* - b_2), and zero loss whenever the two solutions share an exposure or the second stage reaches
the target.
"""
import itertools
import sys

import cvxpy as cp
import numpy as np

LAM = np.array([0.0184, 0.00897])
SIZES = np.array([0.0854, 0.0610])
SIG_F = np.diag(SIZES ** 2)
BA = np.array([1.0, 0.3])
GEOS = {"G1-exact": [np.array([1.0, 0.0]), np.array([1.0, 0.3])],
        "G2-missing": [np.array([1.0, 0.0])],
        "G3-infeasible": [np.array([1.0, 0.0]), np.array([1.0, 0.15])]}
COSTS = {"Z": 0.0, "EQ5": 0.0005}
TOL = 2e-6


class Cell:
    def __init__(self, geo, cost, alpha, gamma=5.0, resA=0.01, resE=0.002, drag=1e-4):
        self.BE = GEOS[geo]; n = len(self.BE)
        self.B = np.vstack([BA] + self.BE)                 # rows: instruments, cols: factors
        self.alpha, self.gamma = alpha, gamma
        self.drag = np.full(n, drag)
        self.rates = np.array([cost] + [cost] * n)
        self.res = np.array([resA ** 2] + [resE ** 2] * n)   # independent residual shocks: C(w) = 0
        self.Sigma = self.B @ SIG_F @ self.B.T + np.diag(self.res)
        self.x0 = np.array([0.5, 0.4] + [0.0] * (n - 1)); self.h0 = 0.1
        self.cap = np.ones(1 + n)
        self.mu_res = np.array([self.alpha] + list(-self.drag))

    def fees(self, w):
        u = w - self.x0
        return self.rates @ cp.pos(u) + self.rates @ cp.pos(-u)

    def fees_np(self, w):
        u = w - self.x0
        return self.rates @ np.maximum(u, 0) + self.rates @ np.maximum(-u, 0)

    def feasible(self, w):
        return [w >= 0, w <= self.cap, self.h0 - cp.sum(w - self.x0) - self.fees(w) >= 0]

    def b(self, w):
        return self.B.T @ w

    def G(self, b):
        return b @ LAM - self.gamma / 2 * b @ SIG_F @ b

    def Hexpr(self, w):
        return self.mu_res @ w - self.gamma / 2 * cp.sum(cp.multiply(self.res, cp.square(w))) - self.fees(w)

    def Qexpr(self, w):
        b = self.b(w)
        return b @ LAM - self.gamma / 2 * cp.quad_form(b, SIG_F) + self.Hexpr(w)

    def Q_np(self, w):
        return self.b(w) @ LAM + self.mu_res @ w - self.gamma / 2 * w @ self.Sigma @ w - self.fees_np(w)

    def S_np(self, w, bstar):
        d = self.b(w) - bstar
        return (self.mu_res @ w - self.fees_np(w)
                - self.gamma / 2 * (d @ SIG_F @ d + self.res @ (w ** 2)))

    def Sexpr(self, w, bstar):
        d = self.b(w) - bstar
        return self.Hexpr(w) - self.gamma / 2 * cp.quad_form(d, SIG_F)

    def solve(self, obj, cons):
        w = cp.Variable(1 + len(self.BE))
        prob = cp.Problem(cp.Maximize(obj(w)), cons(w))
        prob.solve(solver="CLARABEL")
        assert prob.status in ("optimal", "optimal_inaccurate"), prob.status
        return prob.value, np.array(w.value)

    def stage1(self, over):
        obj = lambda w: self.b(w) @ LAM - self.gamma / 2 * cp.quad_form(self.b(w), SIG_F)
        if over == "R0":
            _, w1 = self.solve(obj, lambda w: [w >= 0, cp.sum(w) <= 1])
        else:
            _, w1 = self.solve(obj, self.feasible)
        return self.b(w1)

    def run(self, over="R0"):
        J, wJ = self.solve(self.Qexpr, self.feasible)
        bJ = self.b(wJ)
        bstar = self.stage1(over)
        nu = LAM - self.gamma * SIG_F @ bstar
        _, w2 = self.solve(lambda w: self.Sexpr(w, bstar), self.feasible)
        b2 = self.b(w2)
        Ts = self.Q_np(w2)
        # fibre-confined stage 2 (claim 027), if the fibre is nonempty
        try:
            V, wT = self.solve(self.Hexpr, lambda w: self.feasible(w) + [cp.abs(self.b(w) - bstar) <= 1e-9])
            T = self.G(bstar) + V
        except AssertionError:
            T = None
        return dict(J=J, wJ=wJ, bJ=bJ, bstar=bstar, nu=nu, w2=w2, b2=b2, Ts=Ts, loss=J - Ts, T=T)


def main():
    rng = np.random.default_rng(28)
    zero, pos = 0, 0
    for geo, cost, alpha in itertools.product(GEOS, COSTS, [-0.005, -0.0025, 0.0, 0.0025, 0.005]):
        c = Cell(geo, COSTS[cost], alpha)
        for over in ("R0", "bF"):
            r = c.run(over)
            nu, de, dw = r["nu"], r["bJ"] - r["b2"], r["wJ"] - r["w2"]
            # part 1: identity at random feasible-or-not holdings
            for _ in range(5):
                w = rng.uniform(0, 1, size=len(r["w2"]))
                lhs = c.S_np(w, r["bstar"]); rhs = c.Q_np(w) - nu @ c.b(w) - c.gamma / 2 * r["bstar"] @ SIG_F @ r["bstar"]
                assert abs(lhs - rhs) < 1e-12, (geo, cost, alpha, lhs, rhs)
            # containment of b_J in R and stage-1 optimality
            assert nu @ (r["bJ"] - r["bstar"]) <= TOL, (geo, cost, alpha, over, nu @ (r["bJ"] - r["bstar"]))
            # part 2
            assert -TOL <= r["loss"] <= nu @ de + TOL, (geo, cost, alpha, over, r["loss"], nu @ de)
            assert nu @ de <= nu @ (r["bstar"] - r["b2"]) + TOL
            # part 3
            assert r["loss"] <= nu @ de - c.gamma / 2 * dw @ c.Sigma @ dw + TOL, (geo, cost, alpha, over)
            # part 4
            if r["T"] is not None:
                assert r["loss"] <= (r["J"] - r["T"]) + nu @ (r["bstar"] - r["b2"]) + TOL, (geo, cost, alpha, over)
            # zero loss when the two solutions share an exposure, or when the target is reached
            if np.linalg.norm(de) < 1e-6 or np.linalg.norm(r["b2"] - r["bstar"]) < 1e-6:
                assert abs(r["loss"]) < TOL, (geo, cost, alpha, over, r["loss"]); zero += 1
            elif r["loss"] > TOL:
                pos += 1
            if over == "R0":
                print(f"  {geo:14s} {cost:4s} alpha {alpha * 1e4:+5.0f} bp: loss {r['loss'] * 1e4:7.3f} bp, "
                      f"nu'de {nu @ de * 1e4:7.3f} bp, |nu| {np.linalg.norm(nu) * 1e4:5.1f} bp, |de| {np.linalg.norm(de):.4f}, "
                      f"fibre loss {'n/a' if r['T'] is None else f'{(r['J'] - r['T']) * 1e4:.3f} bp'}")
    print(f"  shared exposure or target reached, with zero loss, in {zero} solves; positive loss in {pos}")
    assert pos > 0 and zero > 0
    print("checks/028: all checks passed")


if __name__ == "__main__":
    main()
    sys.exit(0)
