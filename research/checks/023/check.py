"""Finite checks for claim 023; not its proof.

Run: uv run python checks/023/check.py

Part A (random small M3 instances, one ETF, two latent parameters, zero or
independent residual shocks): for the four root optimizers and random root
actions, the node certainty equivalents c^N_y (closed form) and c^E_y (a node
solve) are computed, and the exact node decomposition
phi = -(1/rho) ln sum_y w_y exp(-rho G_y) is checked against the premium
computed by a fixed-root solve (claim 022's check). The node lower bounds
(sure-sign and risk-adjusted) and the node caps are checked against the exact
node gains, and alpha <= phi <= beta_node <= beta (claim 022's cap).

Part B (the two certifications): the sure-active family at zero rates
(alpha(B_N) against beta_node(A_E) = 0) and claim 012's family at zero rates
(the robust lower bound with u = (7/15, 8/15)) against numerically solved
channels.

Part C (six of experiment 015's one-ETF instances, zero costs): the node
bounds and the premia at the four optimizers, the ratios alpha/phi and
beta_node/phi, and whether either sufficient condition certifies the
channel's sign there (reported, not asserted).

Floating CLARABEL solves, not certificates.
"""
import importlib.util
import itertools
import math
import random
import sys
from fractions import Fraction as Fr
from pathlib import Path

import cvxpy as cp
import numpy as np

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("c022", HERE.parent / "022" / "check.py")
c022 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(c022)
Instance = c022.Instance


# ---------------------------------------------------------------- node objects
def post_root(inst, u0):
    u0 = np.array(u0, float)
    fee = np.array(inst.rates[:2]) @ np.maximum(u0, 0) + np.array(inst.rates[2:]) @ np.maximum(-u0, 0)
    h = inst.h0 - u0.sum() - fee
    return max(h, 0.0), np.maximum(inst.x0 + u0, 0.0)


def node_paths(inst, node):
    """Paths through a public observation: (mass, posterior-weighted second-quarter gross returns)."""
    k0, s0 = node[0]
    gA0, gE0, _ = inst.g[k0, s0]
    P0 = sum(float(inst.prior[k] * inst.q[s]) for k, s in node)
    rows = []
    for k, s0_ in node:
        for s1, _ in enumerate(inst.scen):
            gA1, gE1, _ = inst.g[k, s1]
            rows.append((float(inst.prior[k] * inst.q[s0_] * inst.q[s1]) / P0, float(gA1), float(gE1)))
    return P0, float(gA0), float(gE0), rows


def node_values(inst, u0):
    """Per node: P0, c^N_y, c^E_y (node solve), lower bounds and cap on the node gain."""
    rho = float(inst.rho)
    h, x = post_root(inst, u0)
    kbE, ksE = float(inst.rates[1]), float(inst.rates[3])
    out = []
    for node in inst.nodes:
        P0, gA0, gE0, rows = node_paths(inst, node)
        mA, mE = x[0] * gA0, x[1] * gE0
        WN = np.array([h + mA * gA + mE * gE for _, gA, gE in rows])
        pr = np.array([p for p, _, _ in rows])
        gE1 = np.array([gE for _, _, gE in rows])
        cN = -math.log(pr @ np.exp(-rho * (WN - 1))) / rho + 1
        # node solve: ETF-only trade u in [-mE, h/(1+kbE)]
        u = cp.Variable()
        cash = h - u - kbE * cp.pos(u) - ksE * cp.pos(-u)
        W = cash + mA * np.array([gA for _, gA, _ in rows]) + (mE + u) * gE1
        prob = cp.Problem(cp.Minimize(pr @ cp.exp(-rho * (W - 1))), [mE + u >= 0, cash >= 0])
        prob.solve(solver="CLARABEL")
        cE = -math.log(prob.value) / rho + 1
        # bounds
        gmax, gmin = gE1.max(), gE1.min()
        up, down = max(gmax - 1, 0), max(1 - gmin, 0)
        cap = h * up + mE * (up + down)
        lb = 0.0
        # sure-sign
        if gmin > 1 + kbE:
            lb = max(lb, h * ((gmin) / (1 + kbE) - 1))
        if gmax < 1 - ksE:
            lb = max(lb, mE * (1 - ksE - gmax))
        # risk-adjusted first-order with curvature
        tilt = pr * np.exp(-rho * (WN - 1)); tilt /= tilt.sum()
        s2 = ((gmax - gmin) / 2) ** 2
        rbuy = tilt @ ((gE1 - 1 - kbE) / (1 + kbE))
        rsell = tilt @ (1 - ksE - gE1)
        for r, cap_amt in ((rbuy, h), (rsell, mE)):
            if r > 0 and cap_amt > 0:
                lb = max(lb, (r * r / (2 * rho * s2)) if (s2 > 0 and r / (rho * s2) <= cap_amt) else
                         (r * cap_amt - rho * s2 * cap_amt ** 2 / 2))
        out.append(dict(P0=P0, cN=cN, cE=cE, G=cE - cN, lb=lb, cap=cap))
    return out


def aggregate(inst, nodes, key):
    rho = float(inst.rho)
    wts = np.array([n["P0"] * math.exp(-rho * n["cN"]) for n in nodes]); wts /= wts.sum()
    return -math.log(wts @ np.exp(-rho * np.array([n[key] for n in nodes]))) / rho


def part_a():
    rng = random.Random(23)
    TOL = 3e-4
    n = 0
    for trial in range(30):
        inst = c022.random_instance(rng)
        ce, A, B = {}, {}, {}
        for R in ("N", "E"):
            ce["F", R], A[R] = inst.solve("F", R)
            ce["E", R], B[R] = inst.solve("E", R)
        roots = [A["N"], A["E"], B["N"], B["E"]] + [np.array([rng.uniform(0, 0.8), rng.uniform(0, 0.2)])]
        for u0 in roots:
            u0 = np.maximum(u0, 0.0) * (1 - 1e-7)
            cE, _ = inst.solve(None, "E", u0_fixed=u0); cN, _ = inst.solve(None, "N", u0_fixed=u0)
            phi = cE - cN
            nodes = node_values(inst, u0)
            assert abs(aggregate(inst, nodes, "G") - phi) < TOL, (trial, aggregate(inst, nodes, "G"), phi)
            for nd in nodes:
                assert nd["lb"] - 1e-6 <= nd["G"] + TOL <= nd["cap"] + TOL + 1e-6 + nd["G"], (trial, nd)
                assert nd["G"] <= nd["cap"] + TOL, (trial, nd)
            alpha, beta_node = aggregate(inst, nodes, "lb"), aggregate(inst, nodes, "cap")
            assert alpha - TOL <= phi <= beta_node + TOL, (trial, alpha, phi, beta_node)
            assert beta_node <= inst.beta(u0) + 1e-9, (trial, beta_node, inst.beta(u0))
            n += 1
    print(f"part A: node decomposition, node bounds and alpha <= phi <= beta_node <= beta hold at {n} root actions")


def part_b():
    # sure-active family, zero rates
    thetas = [(Fr(1, 2), Fr(1, 2), Fr(0)), (Fr(1, 2), Fr(-1, 2), Fr(0))]
    scen, q = [((Fr(0), Fr(0)), Fr(0), Fr(0))], [Fr(1)]
    inst = Instance(thetas, [Fr(1, 3), Fr(2, 3)], scen, q, (Fr(1), Fr(0)), (Fr(0), Fr(1)), Fr(0), (Fr(0),) * 4, 20)
    ce = {}
    for R in ("N", "E"):
        ce["F", R], _ = inst.solve("F", R, shift=2.25); ce["E", R], _ = inst.solve("E", R)
    chan = (ce["F", "E"] - ce["E", "E"]) - (ce["F", "N"] - ce["E", "N"])
    alpha_BN = aggregate(inst, node_values(inst, [0.0, 0.0]), "lb")
    beta_AE = aggregate(inst, node_values(inst, [1.0, 0.0]), "cap")
    formula = (math.log(1.5) - math.log(1 + math.exp(-10) / 2)) / 20
    assert abs(alpha_BN - formula) < 1e-9 and beta_AE < 1e-12
    assert chan <= beta_AE - alpha_BN + 1e-5 and formula > 1 / 50
    print(f"part B1: sure-active family, channel {chan:+.6f} <= beta_node(A_E) - alpha(B_N) = {beta_AE - alpha_BN:+.6f} < -1/50")
    # claim 012 family, zero rates
    thetas = [(Fr(1, 2), Fr(-1, 2), Fr(0)), (Fr(-1, 2), Fr(1, 2), Fr(0))]
    inst = Instance(thetas, [Fr(1, 2), Fr(1, 2)], scen, q, (Fr(1), Fr(0)), (Fr(0), Fr(1)), Fr(0), (Fr(0),) * 4, 20)
    for R in ("N", "E"):
        ce["F", R], _ = inst.solve("F", R, shift=1.25); ce["E", R], _ = inst.solve("E", R)
    chan = (ce["F", "E"] - ce["E", "E"]) - (ce["F", "N"] - ce["E", "N"])
    u = [7 / 15, 8 / 15]
    nodes = node_values(inst, u)
    alpha_u = aggregate(inst, nodes, "lb")
    cN_u, _ = inst.solve(None, "N", u0_fixed=u)
    penalty = 1.25 - cN_u
    beta_BE = aggregate(inst, node_values(inst, [0.0, 0.0]), "cap")
    bound = alpha_u - penalty - beta_BE
    # closed forms from the claim
    wplus = 1 / (1 + math.exp(-8 / 3))
    alpha_formula = -math.log(wplus * math.exp(-20 * 2 / 15) + (1 - wplus)) / 20
    cN_formula = 1 - math.log((math.exp(-20 * (71 / 60 - 1)) + math.exp(-20 * (79 / 60 - 1))) / 2) / 20
    beta_formula = -math.log((1 + math.exp(-10)) / 2) / 20
    assert abs(alpha_u - alpha_formula) < 1e-9 and abs(cN_u - cN_formula) < 1e-5 and abs(beta_BE - beta_formula) < 1e-9
    assert bound > 3 / 100 and chan >= bound - 1e-5
    print(f"part B2: claim 012 family, channel {chan:+.6f} >= alpha(u) - penalty - beta_node(B_E) = {bound:+.6f} > 3/100")


def part_c():
    ROOT = HERE.parent.parent
    _s3 = importlib.util.spec_from_file_location("exp015p", ROOT / "checks" / "exp015-premia" / "check.py")
    exp015p = importlib.util.module_from_spec(_s3); _s3.loader.exec_module(exp015p)
    sys.path.insert(0, str(ROOT / "checks" / "red-m3-definition"))
    from check import bayes, returns  # noqa: E402
    exp015, red008 = exp015p.exp015, exp015p.red008
    certified = 0
    ratios_lb, ratios_cap = [], []
    for rho, tilt in itertools.product(exp015.RHOS, exp015.TILTS):
        I = exp015.instance("1 ETF (1,0)", "zero", rho, exp015.TILTS[tilt])
        B = bayes(I); Y, P0, post = B
        r = float(I["rho"]); x0 = np.array([float(v) for v in I["x0"]]); h0 = float(I["h0"])
        ce, opt = {}, {}
        for D, R in [("F", "N"), ("E", "N"), ("F", "E"), ("E", "E")]:
            V, u0 = red008.solve(I, B, D, R)
            if V is None:
                V, u0 = red008.solve(I, B, D, R, solver="SCS", eps_abs=1e-10, eps_rel=1e-10, max_iters=200000)
            ce[D, R] = float(red008.ce(V, I["rho"])) / 1e4; opt[D, R] = np.array(u0, float)
        chan = (ce["F", "E"] - ce["E", "E"]) - (ce["F", "N"] - ce["E", "N"])

        def bounds(u0):
            h = h0 - u0.sum(); x = np.maximum(x0 + u0, 0)
            lbs, caps, w = [], [], []
            for y in Y:
                if P0[y] == 0:
                    continue
                g0 = np.array([1 + float(v) for v in y[1]]); m = x * g0
                rows, pr = [], []
                for t, pt in post[y].items():
                    if pt > 0:
                        for s_ in I["shocks"]:
                            rows.append([1 + float(v) for v in returns(I, t, s_)[1]]); pr.append(float(pt * s_[0]))
                rows, pr = np.array(rows), np.array(pr)
                WN = h + rows @ m
                cN = -math.log(pr @ np.exp(-r * (WN - 1))) / r + 1
                gE = rows[:, 1]; gmax, gmin = gE.max(), gE.min()
                up, down = max(gmax - 1, 0), max(1 - gmin, 0)
                tilt_ = pr * np.exp(-r * (WN - 1)); tilt_ /= tilt_.sum()
                s2 = ((gmax - gmin) / 2) ** 2
                lb = 0.0
                for rr, amt in ((tilt_ @ (gE - 1), h), (tilt_ @ (1 - gE), m[1])):
                    if rr > 0 and amt > 0:
                        lb = max(lb, rr * rr / (2 * r * s2) if rr / (r * s2) <= amt else rr * amt - r * s2 * amt ** 2 / 2)
                lbs.append(lb); caps.append(h * up + m[1] * (up + down)); w.append(float(P0[y]) * math.exp(-r * cN))
            w = np.array(w) / sum(w)
            agg = lambda v: -math.log(w @ np.exp(-r * np.array(v))) / r
            return agg(lbs), agg(caps)

        def premium(u0):
            cE, _ = exp015p.solve_fixed(I, B, u0, "E"); cN, _ = exp015p.solve_fixed(I, B, u0, "N")
            return cE - cN
        vals = {}
        for name, u0 in (("A_N", opt["F", "N"]), ("A_E", opt["F", "E"]), ("B_N", opt["E", "N"]), ("B_E", opt["E", "E"])):
            a, b = bounds(u0); ph = premium(u0)
            vals[name] = (a, b, ph)
            assert a - 3e-5 <= ph <= b + 3e-5, (rho, tilt, name, a, ph, b)
            if ph > 1e-5:
                ratios_lb.append(a / ph); ratios_cap.append(b / ph)
        neg_cert = vals["A_E"][1] < vals["B_N"][0]; pos_cert = vals["A_N"][0] > vals["B_E"][1]
        ok = (chan < 0 and neg_cert) or (chan > 0 and pos_cert)
        certified += int(ok)
        fmt = lambda t: f"{t[0] * 1e4:.2f}/{t[2] * 1e4:.2f}/{t[1] * 1e4:.2f}"
        print(f"  rho {int(rho):2d}, {tilt}: channel {chan * 1e4:+.2f} bp; alpha/phi/beta_node (bp) at "
              f"A_N {fmt(vals['A_N'])}, A_E {fmt(vals['A_E'])}, B_N {fmt(vals['B_N'])}, B_E {fmt(vals['B_E'])}; "
              f"certified: {'yes' if ok else 'no'}")
    print(f"part C: alpha/phi in [{min(ratios_lb):.2f}, {max(ratios_lb):.2f}], beta_node/phi in "
          f"[{min(ratios_cap):.0f}, {max(ratios_cap):.0f}] where phi > 0; {certified} of 6 signs certified by the node conditions")
    assert 0.6 <= min(ratios_lb) and max(ratios_lb) <= 1.0 + 1e-6 and min(ratios_cap) >= 20


if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    print("checks/023: all checks passed")
    sys.exit(0)
