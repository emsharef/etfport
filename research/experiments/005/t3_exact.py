"""Experiment 005, Deviation 3: T3 recomputed with exact bands, replacing the float-bisection harness.

Replays the registered RNG stream (seed 2005; T1 and T2 run first exactly as in run.main, so T3 sees the
same draws), keeps T3's registered draw loop and inclusion rules, and computes each band by bisection in
exact rational arithmetic with the experiment 004 solver in exact mode:
    L = inf{alpha : a*(alpha) >= a0},  U = inf{alpha : a*(alpha) > a0},
bracketed to 2^-40 x 0.1 (about 1e-13) inside ALPHA_RANGE. Every predicate evaluation is an exact solve, so
the brackets are certified; the only dependency is the monotonicity of a* in alpha (the revealed-preference
argument in the Question, which red checked). Each lam_2 gives a certified width interval
[U_lo - L_hi, U_hi - L_lo]. A counterexample is two disjoint intervals; overlapping intervals are reported as
"no difference detectable at this resolution", never as a confirmation of T3. Inclusion needs exact
bracketing: a*(-5%) < a0 and a*(+5%) > a0 at both lam_2 values.
"""
from __future__ import annotations

import sys
import time
from dataclasses import replace
from fractions import Fraction as Fr
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import run as r  # noqa: E402

STEPS = 40


def a_ex(I, alpha):
    return r.solve(replace(I, alpha=alpha), "F", exact=True)[1][0]


def edge(I, pred):
    """Smallest alpha in ALPHA_RANGE with pred(a*(alpha)); returns a certified bracket (x, y]: not pred at x, pred at y."""
    x, y = r.ALPHA_RANGE
    for _ in range(STEPS):
        m = (x + y) / 2
        if pred(a_ex(I, m)):
            y = m
        else:
            x = m
    return x, y


def exact_band(I):
    a0 = I.w0[0]
    lo, hi = r.ALPHA_RANGE
    if not (a_ex(I, lo) < a0 and a_ex(I, hi) > a0):
        return None
    Lx, Ly = edge(I, lambda a: a >= a0)
    Ux, Uy = edge(I, lambda a: a > a0)
    return (Lx, Ly), (Ux, Uy), (Ux - Ly, Uy - Lx)


def main() -> None:
    t0 = time.time()
    rng = np.random.default_rng(r.SEED)
    r.t1(rng)
    r.t2(rng)
    stats, examples = {}, []
    for _ in range(r.N_T3):                                  # the registered T3 draw loop
        n = 1 + int(rng.integers(2))
        fam, I = r.draw(rng, n, interior_active=True)
        Is = [replace(I, lam=(I.lam[0], l2)) for l2 in r.T3_LAM2]
        if any(r.check_instance(replace(J, alpha=x)) for J in Is for x in r.ALPHA_RANGE):
            continue
        s = stats.setdefault((fam, n), [0, 0, 0])
        bands = [exact_band(J) for J in Is]
        if any(b is None for b in bands):
            s[2] += 1
            continue
        s[0] += 1
        (w0lo, w0hi), (w1lo, w1hi) = bands[0][2], bands[1][2]
        if w0hi < w1lo or w1hi < w0lo:
            s[1] += 1
            examples.append((fam, n, Is, bands))
    print("### T3 with exact bands (Deviation 3)\n")
    print("| Cost family | n | Instances with both bands bracketed | Certified counterexamples | "
          "Skipped (band not bracketed) |\n|---|---|---|---|---|")
    for (fam, n), (k, c, sk) in sorted(stats.items()):
        print(f"| {fam} | {n} | {k} | {c} | {sk} |")
    print("\nCertified width differences (bp per quarter, lower bound of |W(0) - W(1/100)|):\n")
    print("| Cost family | n | Min | Max |\n|---|---|---|---|")
    by = {}
    for fam, n, Is, bands in examples:
        (a, b), (c, d) = bands[0][2], bands[1][2]
        gap = max(c - b, a - d)
        by.setdefault((fam, n), []).append(gap)
    for k, v in sorted(by.items()):
        print(f"| {k[0]} | {k[1]} | {float(min(v)) * 1e4:.5f} | {float(max(v)) * 1e4:.3f} |")
    etfc = [e for e in examples if e[0] == "ETFC"]
    if etfc:
        fam, n, Is, bands = etfc[0]
        print(f"\nFirst ETFC counterexample: {r.show(Is[0])} (lam_2 varied).")
        for J, (Lb, Ub, W) in zip(Is, bands):
            print(f"- lam_2 = {J.lam[1]}: L in ({float(Lb[0]):.12f}, {float(Lb[1]):.12f}], "
                  f"U in ({float(Ub[0]):.12f}, {float(Ub[1]):.12f}]; width in [{float(W[0]) * 1e4:.6f}, "
                  f"{float(W[1]) * 1e4:.6f}] bp")
    print(f"\nseconds: {time.time() - t0:.0f}")


if __name__ == "__main__":
    main()
