"""Finite checks for claim 026 (the refile of refuted claims 024 and 025); not its proof.

Run: uv run python checks/026/check.py

Part A (range-type caps cannot be sharp): at a node with cash h, marked ETF
value m, and ETF returns supported on {gmin, gmax}, the two-point law with
mass 1-eta at gmax and eta at gmin has gain approaching h((gmax)/(1+kappa^+)-1)
as eta -> 0, so any cap depending only on (h, m, gmax, gmin, rates, rho) is at
least that; the mirror with mass at gmin gives m(1-kappa^- - gmin).

Part B (mean-type caps are valid): on random nodes (2-5 paths, one ETF, buy
and sell rates up to 2%, rho in {1, 5, 20}), the exact node gain (a node
solve) is at most the tangent cap max(r^+ h, r^- m, 0) and at most the
curvature cap q(r, v_min), and at least claim 023's lower bound q(r, s^2);
at nodes with r^+ <= 0 and r^- <= 0 the exact gain is zero.

Part C (experiment 015's six zero-cost one-ETF instances): beta_mean at the
four optimizers, against the premia, and whether the sufficient sign
conditions with beta_mean in place of beta_node certify the channel's sign.
It also prints, at the rho = 20 ETF-only optimizers, the per-node favorable
directions r^+, r^- and the marked ETF value m(y) (red's refutation of claim
024: every node has a favorable selling direction but nothing to sell), and
the aggregated range-type lower bound of part 1 at the full-root optimizers.

Part D (red's two counterexamples to claim 025, now covered): a sure ETF
return 1.1 with a 2 percent purchase rate, where the buy-side curvature cap
with the per-cash-dollar payoff and range h equals the gain h Z (a range of
h/(1+kappa^+) would undercut it); and a two-ETF node with no cash, nothing of
the favorable ETF and a favorable switch out of the other, where the node
gain is 0.03626 > 0 although no single purchase or sale is favorable, and
the switch condition r^-_k + (1-kappa^-_k) r^+_j > 0 detects it.

Floating CLARABEL solves, not certificates.
"""
import importlib.util
import itertools
import math
import random
import sys
from pathlib import Path

import cvxpy as cp
import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def node_gain(h, m, rows, pr, rho, kb, ks):
    """Exact node gain for one ETF: rows = [(gA, gE)], pr masses; active marked value folded into W0."""
    WN = np.array([h + m * gE for gA, gE in rows]) + np.array([gA for gA, gE in rows])  # gA here = active marked value times return
    pr = np.array(pr)
    cN = -math.log(pr @ np.exp(-rho * (WN - 1))) / rho + 1
    u = cp.Variable()
    cash = h - u - kb * cp.pos(u) - ks * cp.pos(-u)
    W = cash + np.array([gA for gA, gE in rows]) + (m + u) * np.array([gE for gA, gE in rows])
    prob = cp.Problem(cp.Minimize(pr @ cp.exp(-rho * (W - 1))), [m + u >= 0, cash >= 0])
    prob.solve(solver="CLARABEL")
    cE = -math.log(prob.value) / rho + 1
    return cE - cN, WN, cN


def q(r, v, amt, rho):
    if r <= 0 or amt <= 0:
        return 0.0
    if v <= 0:
        return r * amt
    return r * r / (2 * rho * v) if r / (rho * v) <= amt else r * amt - rho * v * amt ** 2 / 2


def mean_caps(h, m, rows, pr, rho, kb, ks, WN):
    pr = np.array(pr); gE = np.array([gE for _, gE in rows])
    tilt = pr * np.exp(-rho * (WN - 1)); tilt /= tilt.sum()
    Zb = (gE - 1 - kb) / (1 + kb); Zs = 1 - ks - gE
    rb, rs = float(tilt @ Zb), float(tilt @ Zs)
    tangent = max(rb * h, rs * m, 0.0)
    # curvature cap: tilted variance >= exp(-rho (dW + 2 s eps)) Var_q(Z)
    s = (gE.max() - gE.min()) / 2
    curv = 0.0
    for r, amt, Z in ((rb, h, Zb), (rs, m, Zs)):
        if r > 0 and amt > 0:
            dW = WN.max() - WN.min()
            vq = float(pr @ (Z - pr @ Z) ** 2)
            vmin = math.exp(-rho * (dW + 2 * s * amt)) * vq
            curv = max(curv, q(r, vmin, amt, rho))
    lower = max(q(rb, s * s, h, rho), q(rs, s * s, m, rho))
    return tangent, curv, lower, rb, rs


def part_a():
    rho, kb, ks = 5.0, 0.005, 0.005
    h, m, gmax, gmin = 0.6, 0.3, 1.15, 0.85
    target_buy = h * (gmax / (1 + kb) - 1)
    target_sell = m * (1 - ks - gmin)
    for eta in (0.1, 0.01, 0.001, 0.0001):
        rows = [(0.0, gmax), (0.0, gmin)]
        gb, _, _ = node_gain(h, m, rows, [1 - eta, eta], rho, kb, ks)
        gs, _, _ = node_gain(h, m, rows, [eta, 1 - eta], rho, kb, ks)
        print(f"  eta {eta:g}: buy-heavy gain {gb:.5f} (target {target_buy:.5f}); sell-heavy gain {gs:.5f} (target {target_sell:.5f})")
    assert abs(gb - target_buy) < 2e-3 and abs(gs - target_sell) < 2e-3
    print("part A: two-point laws with the same range approach the sure-sign gains; range-type caps are at least these")


def part_b():
    rng = random.Random(24)
    n, zero_nodes = 0, 0
    for trial in range(300):
        k = rng.randint(2, 5)
        rho = rng.choice([1.0, 5.0, 20.0])
        kb, ks = rng.uniform(0, 0.02), rng.uniform(0, 0.02)
        h, m = rng.uniform(0, 0.8), rng.uniform(0, 0.5)
        rows = [(rng.uniform(0.2, 0.6), rng.uniform(0.8, 1.25)) for _ in range(k)]
        pr = np.random.default_rng(trial).dirichlet(np.ones(k))
        G, WN, _ = node_gain(h, m, rows, pr, rho, kb, ks)
        tangent, curv, lower, rb, rs = mean_caps(h, m, rows, pr, rho, kb, ks, WN)
        TOL = 2e-6
        assert lower - TOL <= G <= tangent + TOL, (trial, lower, G, tangent)
        assert G <= curv + TOL, (trial, G, curv)
        if rb <= 0 and rs <= 0:
            assert abs(G) < 1e-6, (trial, G)
            zero_nodes += 1
        n += 1
    print(f"part B: lower <= gain <= min(tangent, curvature) on {n} random nodes; {zero_nodes} nodes with no favorable direction have zero gain")


RANGE_LB, FULL_PREMIA, CAP_RATIOS = [], [], []


def part_c():
    _s3 = importlib.util.spec_from_file_location("exp015p", ROOT / "checks" / "exp015-premia" / "check.py")
    exp015p = importlib.util.module_from_spec(_s3); _s3.loader.exec_module(exp015p)
    sys.path.insert(0, str(ROOT / "checks" / "red-m3-definition"))
    from check import bayes, returns  # noqa: E402
    exp015, red008 = exp015p.exp015, exp015p.red008
    certified = 0
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

        def caps(u0, evidence=False):
            h = h0 - u0.sum(); x = np.maximum(x0 + u0, 0)
            tans, curvs, lows, w, rngs = [], [], [], [], []
            ev = []
            for y in Y:
                if P0[y] == 0:
                    continue
                g0 = np.array([1 + float(v) for v in y[1]]); mk = x * g0
                rows, pr = [], []
                for t, pt in post[y].items():
                    if pt > 0:
                        for s_ in I["shocks"]:
                            gg = [1 + float(v) for v in returns(I, t, s_)[1]]
                            rows.append((mk[0] * gg[0], gg[1])); pr.append(float(pt * s_[0]))
                pr = np.array(pr)
                WN = np.array([h + mk[1] * gE + gA for gA, gE in rows])
                cN = -math.log(pr @ np.exp(-r * (WN - 1))) / r + 1
                tangent, curv, lower, rb, rs = mean_caps(h, mk[1], rows, pr, r, 0.0, 0.0, WN)
                gE = np.array([gE for _, gE in rows])
                rngs.append(max(h * max(gE.max() - 1, 0), mk[1] * max(1 - gE.min(), 0)))
                ev.append((rb, rs, mk[1]))
                tans.append(tangent); curvs.append(min(tangent, curv)); lows.append(lower); w.append(float(P0[y]) * math.exp(-r * cN))
            w = np.array(w) / sum(w)
            agg = lambda v: -math.log(w @ np.exp(-r * np.array(v))) / r
            if evidence:
                rb_min, rs_min, m_max = min(e[0] for e in ev), min(e[1] for e in ev), max(e[2] for e in ev)
                print(f"      evidence at this ETF-only optimizer: r^+ <= {max(e[0] for e in ev):+.4f}, r^- >= {rs_min:+.4f} at every node, marked ETF value <= {m_max:.1e}")
                assert rs_min > 0 and m_max < 1e-8, "red's description: favorable selling direction, nothing to sell"
            return agg(lows), agg(curvs), agg(tans), agg(rngs)
        vals = {}
        for name, u0 in (("A_N", opt["F", "N"]), ("A_E", opt["F", "E"]), ("B_N", opt["E", "N"]), ("B_E", opt["E", "E"])):
            a, bm, bt, rng_lb = caps(u0, evidence=(int(rho) == 20 and name in ("B_N", "B_E")))
            cE, _ = exp015p.solve_fixed(I, B, u0, "E"); cN, _ = exp015p.solve_fixed(I, B, u0, "N")
            ph = cE - cN
            assert a - 3e-5 <= ph <= bm + 3e-5, (rho, tilt, name, a, ph, bm)
            vals[name] = (a, ph, bm, bt)
            if name in ("A_N", "A_E"):
                RANGE_LB.append(rng_lb * 1e4); FULL_PREMIA.append(ph * 1e4)
            if ph > 1e-5:
                CAP_RATIOS.append(bm / ph)
        neg = vals["A_E"][2] < vals["B_N"][0]; pos = vals["A_N"][0] > vals["B_E"][2]
        ok = (chan < 0 and neg) or (chan > 0 and pos)
        certified += int(ok)
        fmt = lambda t: f"{t[0] * 1e4:.2f}/{t[1] * 1e4:.2f}/{t[2] * 1e4:.2f}"
        print(f"  rho {int(rho):2d}, {tilt}: channel {chan * 1e4:+.2f} bp; alpha/phi/beta_mean (bp) at "
              f"A_N {fmt(vals['A_N'])}, A_E {fmt(vals['A_E'])}, B_N {fmt(vals['B_N'])}, B_E {fmt(vals['B_E'])}; certified: {'yes' if ok else 'no'}")
    print(f"part C: {certified} of 6 experiment 015 zero-cost signs certified with the mean-type cap; "
          f"beta_mean/phi in [{min(CAP_RATIOS):.2f}, {max(CAP_RATIOS):.1f}] where phi > 0; part 1's range-type lower bound "
          f"at the full-root optimizers {min(RANGE_LB):.0f}-{max(RANGE_LB):.0f} bp against premia {min(FULL_PREMIA):.2f}-{max(FULL_PREMIA):.2f} bp")
    assert certified == 2 and min(RANGE_LB) > 300 and max(FULL_PREMIA) < 20
    return certified


def part_d():
    # red's counterexample 1: sure return 1.1, kappa^+ = 2/100, h = 1
    rho, kb, ks, h, m = 5.0, 0.02, 0.0, 1.0, 0.0
    rows, pr = [(0.0, 1.1)], [1.0]
    G, WN, _ = node_gain(h, m, rows, pr, rho, kb, ks)
    Zcash = (1.1 - 1 - kb) / (1 + kb)          # per cash dollar
    cap_h = q(Zcash, 0.0, h, rho)               # range h: the corrected cap
    cap_wrong = q(Zcash, 0.0, h / (1 + kb), rho)  # claim 025's range: undercuts
    assert abs(G - h * Zcash) < 1e-6 and cap_h >= G - 1e-9 and cap_wrong < G, (G, cap_h, cap_wrong)
    print(f"part D1: sure return 1.1, kappa 2%: gain {G:.6f}, cap with range h {cap_h:.6f} (valid), with range h/(1+kappa) {cap_wrong:.6f} (undercuts)")
    # red's counterexample 2: two ETFs, zero rates, rho = 5, two equally likely paths
    rho = 5.0
    g1, g2 = np.array([1.3, 1.0]), np.array([1.05, 1.05]); pr = np.array([0.5, 0.5])
    h, m1, m2 = 0.0, 0.0, 0.5
    WN = h + m1 * g1 + m2 * g2                  # constant across paths
    u = cp.Variable(2)
    cash = h - cp.sum(u)
    W = cash + (m1 + u[0]) * g1 + (m2 + u[1]) * g2
    prob = cp.Problem(cp.Minimize(pr @ cp.exp(-rho * (W - 1))), [m1 + u[0] >= 0, m2 + u[1] >= 0, cash >= 0])
    prob.solve(solver="CLARABEL")
    cN = -math.log(pr @ np.exp(-rho * (WN - 1))) / rho + 1
    G2 = -math.log(prob.value) / rho + 1 - cN
    tilt = pr * np.exp(-rho * (WN - 1)); tilt /= tilt.sum()
    r1p, r2s = float(tilt @ (g1 - 1)), float(tilt @ (1 - g2))
    assert h == 0 and m1 == 0 and r2s <= 0 and r1p > 0     # claim 025's condition holds literally
    switch = r2s + (1 - 0.0) * r1p
    assert switch > 0 and G2 > 0.036 and G2 < 0.037, (switch, G2)
    print(f"part D2: two-ETF switch node: r^+_1 {r1p:+.3f}, r^-_2 {r2s:+.3f}, switch value {switch:+.3f} > 0, node gain {G2:.5f} > 0")


if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    part_d()
    print("checks/026: all checks passed")
    sys.exit(0)
