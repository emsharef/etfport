"""Experiment 015's sign flips read through claim 022's sandwich and funded cap; a check, not a proof.

Run: uv run python checks/exp015-premia/check.py

For the 24 one-ETF instances of experiment 015 (INST_A base; four cost schedules, rho in
{5, 10, 20}, two tilts), this check re-solves the four cells (F,N), (E,N), (F,E), (E,E) with
red's reviewed machinery (experiments/008/red_reproduce.py `solve`, checks/red-m3-definition
`make`/`bayes`/`returns`), takes the root optimizers A_N, A_E (full root) and B_N, B_E
(ETF-only root), and computes claim 022's premium of future ETF adjustment
phi(u_0) = c_E(u_0) - c_N(u_0) at each by re-solving the node problems with the root fixed.
It then checks, up to solver tolerance:
- the sandwich phi(A_N) - phi(B_E) <= Delta_E - Delta_N <= phi(A_E) - phi(B_N);
- the funded cap phi <= beta at every optimizer;
- and reports, per instance, the channel sign, the two sandwich ends, the root active trade,
  and the post-root adjustable wealth (cash plus ETF value) at A_E and B_N, to see whether
  the rho = 5 flips are the funded mechanism of claim 022 (a root active purchase that
  lowers the full root's redeployable wealth below the ETF-only root's).
Floating CLARABEL solves, not certificates; experiment 015's certified brackets stand.
"""
from __future__ import annotations

import importlib.util
import itertools
import math
import sys
from fractions import Fraction as F
from pathlib import Path

import cvxpy as cp
import numpy as np

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "checks" / "red-m3-definition"))
from check import bayes, make, returns  # noqa: E402

_spec = importlib.util.spec_from_file_location("red008", ROOT / "experiments" / "008" / "red_reproduce.py")
red008 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(red008)
_spec2 = importlib.util.spec_from_file_location("exp015", ROOT / "experiments" / "015" / "run.py")
exp015 = importlib.util.module_from_spec(_spec2)
_spec2.loader.exec_module(exp015)


def solve_fixed(I, B, u0f, cont):
    """c_cont(u0f): CE of the optimal continuation with the root trade fixed at u0f."""
    Y, P0, post = B
    d = len(I["x0"])
    kb = np.array([float(x) for x in I["kb"]]); ks = np.array([float(x) for x in I["ks"]])
    x0 = np.array([float(x) for x in I["x0"]]); h0 = float(I["h0"]); rho = float(I["rho"])
    u0 = np.array(u0f, float)
    fee0 = kb @ np.maximum(u0, 0) + ks @ np.maximum(-u0, 0)
    h0p = h0 - u0.sum() - fee0
    assert h0p >= -1e-9 and np.all(x0 + u0 >= -1e-9)
    h0p = max(h0p, 0.0)
    fee = lambda u: kb @ cp.pos(u) + ks @ cp.neg(u)
    expo, mass, cons = [], [], []
    for y in Y:
        if P0[y] == 0:
            continue
        x1 = np.array([1 + float(r) for r in y[1]]) * np.maximum(x0 + u0, 0)
        u1 = cp.Variable(d)
        cons += [x1 + u1 >= 0, h0p - cp.sum(u1) - fee(u1) >= 0]
        cons += {"F": [], "E": [u1[0] == 0], "N": [u1 == 0]}[cont]
        rows = []
        for t, pt in post[y].items():
            if pt > 0:
                for s in I["shocks"]:
                    rows.append([1 + float(r) for r in returns(I, t, s)[1]])
                    mass.append(float(P0[y] * pt * s[0]))
        expo.append(-rho * (h0p - cp.sum(u1) - fee(u1) + np.array(rows) @ (x1 + u1) - 1))
    prob = cp.Problem(cp.Minimize(cp.sum(cp.multiply(np.array(mass), cp.exp(cp.hstack(expo))))), cons)
    prob.solve(solver="CLARABEL")
    assert prob.status in ("optimal", "optimal_inaccurate"), prob.status
    return 1 - math.log(prob.value) / rho, h0p


def beta(I, u0f, h0p):
    """Claim 022's funded cap (W_0 = 1): h up + (sum_j p_j) gbar (up + down)."""
    x0 = np.array([float(x) for x in I["x0"]]); u0 = np.array(u0f, float)
    gE = [1 + float(returns(I, t, s)[1][j]) for t in I["Theta"] for s in I["shocks"] for j in range(1, len(x0))]
    gbar, gund = max(gE), min(gE)
    up, down = max(gbar - 1, 0), max(1 - gund, 0)
    p = float(np.sum(np.maximum(x0[1:] + u0[1:], 0)))
    return h0p * up + p * gbar * (up + down)


def main():
    TOL = 2e-5
    rows = []
    for cost, rho, tilt in itertools.product(exp015.COSTS, exp015.RHOS, exp015.TILTS):
        I = exp015.instance("1 ETF (1,0)", cost, rho, exp015.TILTS[tilt])
        B = bayes(I)
        ce, opt = {}, {}
        for D, R in [("F", "N"), ("E", "N"), ("F", "E"), ("E", "E")]:
            V, u0 = red008.solve(I, B, D, R)
            if V is None:   # experiment 015's fallback
                V, u0 = red008.solve(I, B, D, R, solver="SCS", eps_abs=1e-10, eps_rel=1e-10, max_iters=200000)
            assert V is not None, (cost, rho, tilt, D, R)
            ce[D, R] = float(red008.ce(V, I["rho"])) / 1e4   # red008.ce reports basis points
            opt[D, R] = np.array(u0, float)
        phi, adj = {}, {}
        for name, u0 in (("A_N", opt["F", "N"]), ("A_E", opt["F", "E"]), ("B_N", opt["E", "N"]), ("B_E", opt["E", "E"])):
            cE, h = solve_fixed(I, B, u0, "E")
            cN, _ = solve_fixed(I, B, u0, "N")
            phi[name] = cE - cN
            x0 = np.array([float(x) for x in I["x0"]])
            adj[name] = h + float(np.sum(np.maximum(x0[1:] + u0[1:], 0)))
            assert phi[name] >= -TOL, (cost, rho, tilt, name, phi[name])
            assert phi[name] <= beta(I, u0, h) + TOL, (cost, rho, tilt, name, phi[name], beta(I, u0, h))
        chan = (ce["F", "E"] - ce["E", "E"]) - (ce["F", "N"] - ce["E", "N"])
        lo, hi = phi["A_N"] - phi["B_E"], phi["A_E"] - phi["B_N"]
        assert lo - TOL <= chan <= hi + TOL, (cost, rho, tilt, lo, chan, hi)
        rows.append(dict(cost=cost, rho=int(rho), tilt=tilt, chan=chan * 1e4, lo=lo * 1e4, hi=hi * 1e4,
                         aN=opt["F", "N"][0], aE=opt["F", "E"][0],
                         adjAE=adj["A_E"], adjBN=adj["B_N"], adjAN=adj["A_N"], adjBE=adj["B_E"],
                         phiAE=phi["A_E"] * 1e4, phiBN=phi["B_N"] * 1e4))
    print("| costs | rho | tilt | channel (bp) | sandwich [lo, hi] (bp) | root active trade under E | adjustable wealth at A_E / B_N | phi(A_E) / phi(B_N) (bp) |")
    print("|---|---|---|---|---|---|---|---|")
    flips_explained = 0; patterns_explained = 0
    for r in rows:
        print(f"| {r['cost']} | {r['rho']} | {r['tilt']} | {r['chan']:+.3f} | [{r['lo']:+.3f}, {r['hi']:+.3f}] | "
              f"{r['aE']:+.4f} | {r['adjAE']:.4f} / {r['adjBN']:.4f} | {r['phiAE']:.3f} / {r['phiBN']:.3f} |")
        if r["chan"] < 0:
            # the negative channel is forced when the full root's premium at A_E is below the ETF root's at B_N
            flips_explained += int(r["hi"] < 0 and r["adjAE"] < r["adjBN"] and r["aE"] > 0)
        else:
            patterns_explained += int(r["lo"] > 0 and r["adjAE"] >= r["adjBN"] - 1e-6 and r["aE"] < 0)
    neg = sum(1 for r in rows if r["chan"] < 0); pos = len(rows) - neg
    print(f"\nnegative channels: {neg}; with upper sandwich end < 0, a root active purchase, and the full root's "
          f"adjustable wealth below the ETF-only root's: {flips_explained}")
    print(f"positive channels: {pos}; with lower sandwich end > 0, a root active sale, and the full root's "
          f"adjustable wealth at least the ETF-only root's: {patterns_explained}")
    assert neg + pos == 24
    print("checks/exp015-premia: sandwich and cap hold on all 24 one-ETF instances of experiment 015")


if __name__ == "__main__":
    main()
    sys.exit(0)
