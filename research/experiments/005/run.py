"""Experiment 005: counterexample search in M2 for three commonly assumed statements (T1-T3).
See experiments/005-m2-counterexample-search.md. Screens with the float mode of experiments/004/m2.py and
certifies every flagged instance with its exact mode. Prints Markdown; the exit code is 0 unless the
code itself fails (finding counterexamples is not a failure).
"""
from __future__ import annotations

import sys
import time
from dataclasses import replace
from fractions import Fraction as Fr
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "004"))
from m2 import Instance2, check_instance, positive_definite, sigma_formula, solve  # noqa: E402

SEED = 2005
N_T1, N_T2, N_T3 = 2000, 1000, 200
TOL = 1e-9                  # float screening tolerance on holdings
EPS = Fr(1, 10 ** 9)        # half-width of exact certification brackets for T3 endpoints
LAM2_GRID = [Fr(k, 400) for k in range(-4, 5)]         # -1% .. +1% per quarter, step 0.25%
T3_LAM2 = (Fr(0), Fr(1, 100))
ALPHA_RANGE = (Fr(-1, 20), Fr(1, 20))
BP = Fr(1, 10000)

G = {
    "b": [Fr(-1, 2), Fr(-1, 4), Fr(0), Fr(1, 4), Fr(1, 2)],
    "e": [Fr(-1, 2), Fr(-1, 4), Fr(1, 4), Fr(1, 2)],
    "sf1": [Fr(3, 50), Fr(2, 25), Fr(1, 10)],
    "sf2": [Fr(1, 50), Fr(3, 100), Fr(1, 25)],
    "sA": [Fr(1, 100), Fr(1, 50), Fr(3, 100)],
    "sE": [Fr(1, 200), Fr(1, 100)],
    "lam1": [Fr(1, 100), Fr(3, 200), Fr(1, 50)],
    "lam2": [Fr(-1, 200), Fr(0), Fr(1, 200), Fr(1, 100)],
    "alpha": [Fr(-1, 200), Fr(-1, 400), Fr(0), Fr(1, 400), Fr(1, 200)],
    "cE": [Fr(-1, 10000), Fr(0), Fr(1, 10000), Fr(5, 10000)],
    "gamma": [Fr(1), Fr(2), Fr(5), Fr(10)],
}
FAMILIES = [("Z", 0.2), ("EQ", 0.3), ("ETFC", 0.3), ("SENS", 0.2)]


def pick(rng, k):
    v = G[k]
    return v[int(rng.integers(len(v)))]


def costs(rng, fam: str, n: int):
    """Cost families (all rates assumed). Z zero; EQ equal everywhere; ETFC ETF-costlier (active 0);
    SENS a hypothetical costlier-active sensitivity (active purchase 25-610 bp; 610 bp is a 575 bp load
    converted to M2's charged amount, experiment 004 B2)."""
    d = 1 + n
    if fam == "Z":
        return (Fr(0),) * d, (Fr(0),) * d
    if fam == "EQ":
        c = [BP, 5 * BP, 25 * BP][int(rng.integers(3))]
        return (c,) * d, (c,) * d
    if fam == "ETFC":
        c = [BP, 5 * BP, 25 * BP][int(rng.integers(3))]
        return (Fr(0),) + (c,) * n, (Fr(0),) + (c,) * n
    kb = [25 * BP, 100 * BP, Fr(23, 377)][int(rng.integers(3))]
    ks = [Fr(0), 100 * BP][int(rng.integers(2))]
    return (kb,) + (BP,) * n, (ks,) + (BP,) * n


def start(rng, d: int, zero_last: bool, interior_active: bool):
    while True:
        u = [int(x) for x in rng.integers(0, 11, size=d + 1)]
        if zero_last:
            u[d - 1] = 0
        if interior_active and u[0] == 0:
            continue
        if sum(u):
            return tuple(Fr(x, sum(u)) for x in u[:d]), Fr(u[d], sum(u))


def draw(rng, n: int, *, zero_last=False, b_pos=False, interior_active=False):
    fam = [f for f, _ in FAMILIES][int(rng.choice(len(FAMILIES), p=[p for _, p in FAMILIES]))]
    while True:
        b = pick(rng, "b")
        if b_pos and b <= 0:
            continue
        BE = ((Fr(1), Fr(0)),) + tuple((Fr(1), pick(rng, "e")) for _ in range(n - 1))
        kb, ks = costs(rng, fam, n)
        w0, k0 = start(rng, 1 + n, zero_last, interior_active)
        I = Instance2(BA=(Fr(1), b), BE=BE, sf=(pick(rng, "sf1"), pick(rng, "sf2")), sA=pick(rng, "sA"),
                      sE=tuple(pick(rng, "sE") for _ in range(n)), lam=(pick(rng, "lam1"), pick(rng, "lam2")),
                      alpha=pick(rng, "alpha"), cE=tuple(pick(rng, "cE") for _ in range(n)),
                      gamma=pick(rng, "gamma"), kbuy=kb, ksell=ks, w0=w0, k0=k0, wbar=(Fr(1),) * (1 + n))
        if not check_instance(I) and positive_definite(sigma_formula(I)):
            return fam, I


def a_star(I, exact=False):
    return solve(I, "F", exact=exact)[1][0]


def drop_second_etf(I: Instance2) -> Instance2:
    return replace(I, BE=I.BE[:1], sE=I.sE[:1], cE=I.cE[:1], kbuy=I.kbuy[:2], ksell=I.ksell[:2],
                   w0=I.w0[:2], wbar=I.wbar[:2])


def show(I: Instance2) -> str:
    f = lambda x: "(" + ", ".join(str(y) for y in x) + ")" if isinstance(x, tuple) else str(x)  # noqa: E731
    parts = [f"B^A={f(I.BA)}", "B^E=" + "; ".join(f(r) for r in I.BE), f"sf={f(I.sf)}", f"sA={I.sA}",
             f"sE={f(I.sE)}", f"lam={f(I.lam)}", f"alpha={I.alpha}", f"c^E={f(I.cE)}", f"gamma={I.gamma}",
             f"kappa+={f(I.kbuy)}", f"kappa-={f(I.ksell)}", f"w0={f(I.w0)}", f"k0={I.k0}"]
    return ", ".join(parts)


def t1(rng):
    """T1: adding a second ETF (not held) never enlarges |a* - a0|."""
    stats, first = {}, {}
    for _ in range(N_T1):
        fam, I2 = draw(rng, 2, zero_last=True)
        I1 = drop_second_etf(I2)
        if check_instance(I1):
            continue
        s = stats.setdefault(fam, [0, 0, 0, 0, 0])
        s[0] += 1
        a0 = float(I2.w0[0])
        d1, d2 = abs(a_star(I1) - a0), abs(a_star(I2) - a0)
        if d2 > d1 + TOL:
            x1, x2 = a_star(I1, True), a_star(I2, True)
            e1, e2 = abs(x1 - I2.w0[0]), abs(x2 - I2.w0[0])
            if e2 > e1:
                s[1] += 1
                if e1 == 0:
                    s[2] += 1
                s[3 if x2 > I2.w0[0] else 4] += 1   # Deviation 1 (reporting only): purchase or sale
                f = first.get(fam)
                if f is None or (e1 == 0 and f[3] != 0):
                    first[fam] = (fam, I2, x2, e1, e2, x1)
    return stats, first


def t2(rng):
    """T2: with B^A_2 > 0, a* is nondecreasing in the belief-mean premium lam_2."""
    stats, first = {}, None
    for _ in range(N_T2):
        n = 1 + int(rng.integers(2))
        fam, I = draw(rng, n, b_pos=True)
        grid = [replace(I, lam=(I.lam[0], l2)) for l2 in LAM2_GRID]
        if any(check_instance(J) for J in grid):
            continue
        s = stats.setdefault((fam, n), [0, 0])
        s[0] += 1
        a = [a_star(J) for J in grid]
        for k in range(len(grid) - 1):
            if a[k + 1] < a[k] - TOL:
                ek, ek1 = a_star(grid[k], True), a_star(grid[k + 1], True)
                if ek1 < ek:
                    s[1] += 1
                    if first is None:
                        first = (fam, grid[k], grid[k + 1], ek, ek1)
                    break
    return stats, first


def band(I: Instance2):
    """Float bisection for the no-active-trade interval in alpha; None if not inside ALPHA_RANGE."""
    a0 = float(I.w0[0])
    at = lambda al: a_star(replace(I, alpha=al))  # noqa: E731
    lo, hi = ALPHA_RANGE
    if not (at(lo) < a0 - TOL and at(hi) > a0 + TOL):
        return None

    def edge(below, above, test):
        x, y = float(below), float(above)
        for _ in range(50):
            m = (x + y) / 2
            if test(at(Fr(m).limit_denominator(10 ** 15))):
                y = m
            else:
                x = m
        return y

    L = edge(lo, hi, lambda a: a >= a0 - TOL)                  # first alpha with no sale
    U = edge(lo, hi, lambda a: a > a0 + TOL)                   # first alpha with a purchase
    return L, U


def certify_band(I: Instance2, L: float, U: float):
    """Exact brackets: a*(L-) < a0 = a*(L+) and a*(U-) = a0 < a*(U+). Returns certified (min, max) width."""
    a0 = I.w0[0]
    Lr, Ur = Fr(L).limit_denominator(10 ** 12), Fr(U).limit_denominator(10 ** 12)
    ex = lambda al: a_star(replace(I, alpha=al), True)  # noqa: E731
    pts = [Lr - EPS, Lr + EPS, Ur - EPS, Ur + EPS]
    if any(check_instance(replace(I, alpha=p)) for p in pts):
        return None
    v = [ex(p) for p in pts]
    if v[0] < a0 and v[1] == a0 and v[2] == a0 and v[3] > a0 and Lr + EPS <= Ur - EPS:
        return (Ur - EPS) - (Lr + EPS), (Ur + EPS) - (Lr - EPS)
    return None


def t3(rng):
    """T3: the width of the no-active-trade band in alpha does not depend on lam_2 (costs alone set it)."""
    stats, first = {}, None
    for _ in range(N_T3):
        n = 1 + int(rng.integers(2))
        fam, I = draw(rng, n, interior_active=True)
        Is = [replace(I, lam=(I.lam[0], l2)) for l2 in T3_LAM2]
        if any(check_instance(replace(J, alpha=x)) for J in Is for x in ALPHA_RANGE):
            continue
        bands = [band(J) for J in Is]
        s = stats.setdefault((fam, n), [0, 0, 0])   # Deviation 2 (reporting only): split by n
        if any(b is None for b in bands):
            s[2] += 1
            continue
        s[0] += 1
        w = [U - L for L, U in bands]
        if abs(w[0] - w[1]) > 1e-6:
            c = [certify_band(J, *b) for J, b in zip(Is, bands)]
            if all(c) and (c[0][1] < c[1][0] or c[1][1] < c[0][0]):
                s[1] += 1
                if first is None:
                    first = (fam, Is, bands, c)
    return stats, first


def main() -> None:
    rng = np.random.default_rng(SEED)
    t0 = time.time()
    s1, f1 = t1(rng)
    print("### T1: adding a second ETF (not held) never enlarges the optimal active trade |a* - a0|\n")
    print("| Cost family | Instances | Certified counterexamples | of which no trade with one ETF | "
          "two-ETF trade is a purchase | two-ETF trade is a sale |\n|---|---|---|---|---|---|")
    for fam, (n, c, z, buy, sell) in sorted(s1.items()):
        print(f"| {fam} | {n} | {c} | {z} | {buy} | {sell} |")
    for fam in sorted(f1):
        _, I2, a2, e1, e2, a1 = f1[fam]
        print(f"\nFirst certified counterexample, family {fam} (a no-trade-with-one-ETF case preferred): {show(I2)}.\n"
              f"a* with one ETF = {a1} (|a* - a0| = {e1}); with two ETFs a* = {a2} (|a* - a0| = {e2}).")

    s2, f2 = t2(rng)
    print("\n### T2: with B^A_2 > 0, a* is nondecreasing in lam_2 (grid -1% .. +1% per quarter, step 0.25%)\n")
    print("| Cost family | n | Instances | Certified counterexamples |\n|---|---|---|---|")
    for (fam, n), (k, c) in sorted(s2.items()):
        print(f"| {fam} | {n} | {k} | {c} |")
    if f2:
        fam, J0, J1, a0_, a1_ = f2
        print(f"\nFirst certified counterexample ({fam}): {show(J0)}.\n"
              f"a* = {a0_} at lam_2 = {J0.lam[1]}; a* = {a1_} at lam_2 = {J1.lam[1]}.")

    s3, f3 = t3(rng)
    print("\n### T3: the no-active-trade band in alpha has the same width at lam_2 = 0 and lam_2 = 1/100\n")
    print("| Cost family | n | Instances with both bands inside [-5%, 5%] | Certified counterexamples | Skipped (band not bracketed) |")
    print("|---|---|---|---|---|")
    for (fam, nn), (n, c, sk) in sorted(s3.items()):
        print(f"| {fam} | {nn} | {n} | {c} | {sk} |")
    if f3:
        fam, Is, bands, c = f3
        print(f"\nFirst certified counterexample ({fam}): {show(Is[0])} (lam_2 varied).")
        for J, (L, U), (wmin, wmax) in zip(Is, bands, c):
            print(f"- lam_2 = {J.lam[1]}: band [{L:.9f}, {U:.9f}] per quarter; certified width in "
                  f"[{float(wmin):.9f}, {float(wmax):.9f}]")
    print(f"\nseconds: {time.time() - t0:.0f}")


if __name__ == "__main__":
    main()
