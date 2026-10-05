"""Finite checks for claim 022; not its proof.

Run: uv run python checks/022/check.py

Part A (the sandwich and the funded cap on random M3 instances). Small M3
instances are drawn at random: two latent parameters, one ETF, one or two
scenarios (zero shocks, or independent +-delta residual shocks so that some
hidden histories share a public observation), random positive returns, prior,
directional rates and rho. Each of the four root/continuation cells (F,N),
(E,N), (F,E), (E,E) is solved as a finite convex program in the root trade and
one node trade per public observation (floating CLARABEL, not a certificate).
The premium of future ETF adjustment phi(u_0) at a fixed root action is
computed by re-solving the node problems with the root fixed. The check
verifies, up to solver tolerance, the sandwich

    phi(A_N) - phi(B_E) <= Delta_E - Delta_N <= phi(A_E) - phi(B_N),

that phi >= 0, and the funded cap phi(u_0) <= beta(u_0) = h (gmax-1)^+ +
p gmax [(gmax-1)^+ + (1-gmin)^+] at the optimizers and at random root actions,
including an all-active root where beta = 0.

Part B (the sure-active family): the exact ingredients of the negative-channel
bound (E[g_E^0 g_E^1] = 11/12, the arithmetic 9/804, ln(3/2) > 2/5, e^9 > 8000)
and numerical solves at all sixteen vertices of the rate box [0, 1/200]^4
confirming Delta_E - Delta_N < -1/125.

These check fixed and random instances; the claim's statements hold for every
M3 instance (parts 1-3) and every rate vector in the box (part 4).
"""
import math
import random
import sys
from fractions import Fraction as Fr

import cvxpy as cp
import numpy as np


# ---------------------------------------------------------------- M3 instance
class Instance:
    """One active fund, one ETF, two factors, K latent parameters, S scenarios, W_0 = 1."""

    def __init__(self, thetas, prior, scen, q, BA, BE, drag, rates, rho, x0=(0.0, 0.0), h0=1.0):
        self.thetas, self.prior, self.scen, self.q = thetas, prior, scen, q
        self.BA, self.BE, self.drag, self.rates, self.rho = BA, BE, drag, rates, rho
        self.x0, self.h0 = np.array(x0, float), float(h0)
        # gross returns g[k][s] = (g_A, g_E)
        self.g = {}
        for k, th in enumerate(thetas):
            for s, (zf, zA, zE) in enumerate(scen):
                f = (th[0] + zf[0], th[1] + zf[1])
                rA = BA[0] * f[0] + BA[1] * f[1] + th[2] + zA
                rE = BE[0] * f[0] + BE[1] * f[1] - drag + zE
                assert 1 + rA > 0 and 1 + rE > 0
                self.g[k, s] = (1 + rA, 1 + rE, f)
        # public observation groups: y = (f, rA, rE) as exact rationals
        groups = {}
        for (k, s), (gA, gE, f) in self.g.items():
            key = (f[0], f[1], gA, gE)
            groups.setdefault(key, []).append((k, s))
        self.nodes = list(groups.values())
        self.gmax_E = max(gE for gA, gE, f in self.g.values())
        self.gmin_E = min(gE for gA, gE, f in self.g.values())

    def fees(self, u):
        buy, sell = np.array(self.rates[:2], float), np.array(self.rates[2:], float)
        return buy @ cp.pos(u) + sell @ cp.pos(-u)

    def solve(self, root, future, u0_fixed=None, shift=1.0):
        """CE of the optimal policy with root class `root` in {F, E} and node class `future`
        in {F, E, N}; with u0_fixed, the root trade is fixed (root class ignored)."""
        rho = float(self.rho)
        if u0_fixed is None:
            u0 = cp.Variable(2)
        else:
            u0 = np.array(u0_fixed, float)
        cash0 = self.h0 - cp.sum(u0) - self.fees(u0) if u0_fixed is None else \
            self.h0 - float(np.sum(u0)) - float(np.array(self.rates[:2]) @ np.maximum(u0, 0)
                                                 + np.array(self.rates[2:]) @ np.maximum(-u0, 0))
        cons = []
        if u0_fixed is None:
            cons += [self.x0 + u0 >= 0, cash0 >= 0]
            if root == "E":
                cons.append(u0[0] == 0)
        obj = 0
        for node in self.nodes:
            u1 = cp.Variable(2)
            cash1 = cash0 - cp.sum(u1) - self.fees(u1)
            # marked incoming holdings are the same for every hidden pair in the node
            k0, s0 = node[0]
            gA0, gE0, _ = self.g[k0, s0]
            incoming = cp.multiply(np.array([float(gA0), float(gE0)]), self.x0 + u0)
            cons += [incoming + u1 >= 0, cash1 >= 0]
            if future == "E":
                cons.append(u1[0] == 0)
            elif future == "N":
                cons.append(u1 == 0)
            for (k, s0_) in node:
                for s1, _ in enumerate(self.scen):
                    gA1, gE1, _ = self.g[k, s1]
                    mass = float(self.prior[k] * self.q[s0_] * self.q[s1])
                    if mass == 0:
                        continue
                    w = cash1 + float(gA1) * (incoming[0] + u1[0]) + float(gE1) * (incoming[1] + u1[1])
                    obj += mass * cp.exp(-rho * (w - shift))
        prob = cp.Problem(cp.Minimize(obj), cons)
        prob.solve(solver="CLARABEL", tol_gap_abs=1e-9, tol_gap_rel=1e-9, tol_feas=1e-9, max_iter=2000)
        assert prob.status in ("optimal", "optimal_inaccurate"), prob.status
        assert prob.value is not None and math.isfinite(prob.value)
        ce = shift - math.log(prob.value) / rho
        uopt = None if u0_fixed is not None else np.array(u0.value, float)
        return ce, uopt

    def beta(self, u0):
        """Funded cap on the ETF-adjustment premium (W_0 = 1):
        h (gmax-1)^+ + p gmax [(gmax-1)^+ + (1-gmin)^+], cash and marked ETF value times the
        ETF's upside and downside relative to cash."""
        u0 = np.array(u0, float)
        h = self.h0 - u0.sum() - (np.array(self.rates[:2]) @ np.maximum(u0, 0)
                                  + np.array(self.rates[2:]) @ np.maximum(-u0, 0))
        p = self.x0[1] + u0[1]
        up = max(float(self.gmax_E) - 1.0, 0.0)
        down = max(1.0 - float(self.gmin_E), 0.0)
        return h * up + p * float(self.gmax_E) * (up + down)


def random_instance(rng):
    lam1 = [Fr(rng.randint(-3, 3), 10) for _ in range(2)]
    lam2 = [Fr(rng.randint(-3, 3), 10) for _ in range(2)]
    al = [Fr(rng.randint(-2, 2), 20) for _ in range(2)]
    thetas = [(lam1[0], lam2[0], al[0]), (lam1[1], lam2[1], al[1])]
    pr = Fr(rng.randint(1, 3), 4)
    prior = [pr, 1 - pr]
    if rng.random() < 0.5:
        scen, q = [((Fr(0), Fr(0)), Fr(0), Fr(0))], [Fr(1)]
    else:
        d = Fr(rng.choice([1, 2]), 20)
        scen = [((Fr(0), Fr(0)), d * sA, d * sE) for sA in (-1, 1) for sE in (-1, 1)]
        q = [Fr(1, 4)] * 4
    BA = (Fr(1), Fr(rng.randint(0, 2), 2))
    BE = (Fr(rng.randint(0, 1)), Fr(1))
    drag = Fr(rng.randint(-1, 1), 100)
    rates = tuple(Fr(rng.choice([0, 1, 5, 10]), 1000) for _ in range(4))
    rho = rng.choice([2, 5, 10])
    return Instance(thetas, prior, scen, q, BA, BE, drag, rates, rho)


def part_a():
    rng = random.Random(22)
    n_ok, n_all_active = 0, 0
    TOL = 3e-4
    for trial in range(40):
        inst = random_instance(rng)
        ce, A, B, phi = {}, {}, {}, {}
        for R in ("N", "E"):
            ce["F", R], A[R] = inst.solve("F", R)
            ce["E", R], B[R] = inst.solve("E", R)
        for name, u0 in (("A_N", A["N"]), ("A_E", A["E"]), ("B_N", B["N"]), ("B_E", B["E"])):
            u0 = np.maximum(u0, 0.0) * (1 - 1e-7)   # a solver optimizer can sit 1e-10 outside the set
            cE, _ = inst.solve(None, "E", u0_fixed=u0)
            cN, _ = inst.solve(None, "N", u0_fixed=u0)
            phi[name] = cE - cN
            assert phi[name] >= -TOL, (trial, name, phi[name])
            assert phi[name] <= inst.beta(u0) + TOL, (trial, name, phi[name], inst.beta(u0))
        dE = ce["F", "E"] - ce["E", "E"]
        dN = ce["F", "N"] - ce["E", "N"]
        lo, hi = phi["A_N"] - phi["B_E"], phi["A_E"] - phi["B_N"]
        assert lo - TOL <= dE - dN <= hi + TOL, (trial, lo, dE - dN, hi)
        # random feasible root actions, including the all-active corner
        for _ in range(3):
            a = rng.uniform(0, 0.9); p = rng.uniform(0, 1 - a) * 0.9
            u0 = np.array([a, p])
            cE, _ = inst.solve(None, "E", u0_fixed=u0); cN, _ = inst.solve(None, "N", u0_fixed=u0)
            assert -TOL <= cE - cN <= inst.beta(u0) + TOL, (trial, u0, cE, cN, cE - cN, inst.beta(u0), inst.rates, inst.rho, inst.gmax_E, inst.gmin_E)
        # the all-active corner: cash exhausted, no ETF -> beta = 0 -> phi = 0
        a_all = 1.0 / (1 + float(inst.rates[0]))
        u0 = np.array([a_all, 0.0])
        cE, _ = inst.solve(None, "E", u0_fixed=u0); cN, _ = inst.solve(None, "N", u0_fixed=u0)
        assert abs(cE - cN) <= TOL and inst.beta(u0) <= 1e-9
        n_all_active += 1
        n_ok += 1
    print(f"part A: sandwich, phi >= 0 and the funded cap hold on {n_ok} random instances; "
          f"the all-active corner has zero premium in all {n_all_active}")


def part_b():
    # exact ingredients
    gE = {0: Fr(3, 2), 1: Fr(1, 2)}
    prior = {0: Fr(1, 3), 1: Fr(2, 3)}
    assert sum(prior[k] * gE[k] ** 2 for k in gE) == Fr(11, 12)
    assert Fr(9, 4) - Fr(9, 4) * Fr(200, 201) == Fr(9, 804)
    assert math.log(1.5) > 0.4 and 0.5 - 0.125 + 1 / 24 - 1 / 64 > 0.4
    assert math.exp(9) > 8000 and 1 + 1 + 0.5 + 1 / 6 + 1 / 24 + 1 / 120 + 1 / 720 > 2.718
    assert Fr(9, 804) - (Fr(1, 50) - Fr(1, 320000)) < -Fr(1, 125)
    # numerical solves on the rate box vertices
    thetas = [(Fr(1, 2), Fr(1, 2), Fr(0)), (Fr(1, 2), Fr(-1, 2), Fr(0))]
    scen, q = [((Fr(0), Fr(0)), Fr(0), Fr(0))], [Fr(1)]
    worst = -1.0
    for bits in range(16):
        rates = tuple(Fr(1, 200) if (bits >> i) & 1 else Fr(0) for i in range(4))
        inst = Instance(thetas, [prior[0], prior[1]], scen, q, (Fr(1), Fr(0)), (Fr(0), Fr(1)), Fr(0), rates, 20)
        assert len(inst.nodes) == 2  # the ETF return reveals the state publicly
        ce = {}
        for R in ("N", "E"):
            ce["F", R], _ = inst.solve("F", R, shift=2.25)   # terminal wealth near 9/4: keep exp values O(1)
            ce["E", R], _ = inst.solve("E", R, shift=1.0)
        ch = (ce["F", "E"] - ce["E", "E"]) - (ce["F", "N"] - ce["E", "N"])
        worst = max(worst, ch)
        assert ch < -1 / 125, (rates, ch)
        assert abs(ce["E", "N"] - 1) < 1e-5 and ce["E", "E"] > 1.0199
        assert ce["F", "N"] >= 450 / 201 - 1e-5 and ce["F", "E"] <= 9 / 4 + 1e-5
    print(f"part B: sure-active family, ETF channel at most {worst:.5f} < -1/125 on all 16 rate-box vertices")


if __name__ == "__main__":
    part_a()
    part_b()
    print("checks/022: all checks passed")
    sys.exit(0)
