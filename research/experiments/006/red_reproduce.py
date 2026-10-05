"""Red's independent reproduction of experiment 006, written from its Design without reading run.py
beyond its calibration constants (which the Design states in words).

Part K: red builds all 900 cells from the Design, solves V_F and V_E with the experiment 004 solver
(exact mode; reproduced by red), and proves every optimum with red's own exact KKT certificate and
red's own mean vector and Sigma (scenario enumeration). Then the Part K tables are recomputed.

Part M: an independent Monte Carlo. Histories are red's own draws (numpy default_rng seeded by
(7006, T, r), not the analyst's seeds), from the Design's law: each shock is +-size with probability 1/2
per quarter, so a sample mean is size * (2 Binomial(T, 1/2) - T) / T. lambda-hat is the factor sample
mean; alpha-hat is the sample mean of r_A - B^A f with the loadings known, i.e. alpha plus the active
residual's sample mean. Policies P1 (ETF-only), P2 (full) and P3 (full, alpha-hat shrunk by T/(T + 40)
when alpha is estimated) are solved with the plug-in belief mean (claim 003) and evaluated with the true
conditional score. The comparison with the report is statistical: per cell, the difference of D means
against the combined standard error.

Usage: uv run python experiments/006/red_reproduce.py [K|M]
"""
import itertools
import sys
from dataclasses import replace
from fractions import Fraction as Fr
from pathlib import Path
from statistics import median

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "004"))
from m2 import Instance2, solve  # noqa: E402  (solver reproduced by red in experiment 004)

BP = Fr(1, 10000)
SF = (Fr(427, 5000), Fr(61, 1000))
LAM = (Fr(23, 1250), Fr(897, 100000))
BA = (Fr(1), Fr(3, 10))
GEOM = {"G1-exact": [(Fr(1), Fr(0)), (Fr(1), Fr(3, 10))], "G2-missing": [(Fr(1), Fr(0))],
        "G3-infeasible": [(Fr(1), Fr(0)), (Fr(1), Fr(3, 20))]}
COSTS = {"Z": (0, 0, 0), "EQ5": (5 * BP, 5 * BP, 5 * BP), "ETFC5": (0, 0, 5 * BP),
         "ETF-stress": (0, 0, 100 * BP), "SENS-load": (Fr(23, 377), 0, BP)}
ALPHA = [Fr(-50), Fr(-25), Fr(0), Fr(25), Fr(50)]
GAMMA = [Fr(2), Fr(5), Fr(10)]
SA = [Fr(1, 100), Fr(1, 50)]
STARTS = {"S1": (Fr(1, 2), Fr(2, 5)), "S2": (Fr(1, 5), Fr(7, 10))}


def cell(geom, cost, alpha_bp, gamma, sA, start):
    E = GEOM[geom]
    n = len(E)
    ka_b, ka_s, ke = (Fr(x) for x in COSTS[cost])
    a0, p0 = STARTS[start]
    return Instance2(BA=BA, BE=tuple(E), sf=SF, sA=sA, sE=(Fr(1, 500),) * n, lam=LAM, alpha=alpha_bp * BP,
                     cE=(BP,) * n, gamma=gamma, kbuy=(ka_b,) + (ke,) * n, ksell=(ka_s,) + (ke,) * n,
                     w0=(a0, p0) + (Fr(0),) * (n - 1), k0=1 - a0 - p0, wbar=(Fr(1),) * (1 + n))


def red_model(I):
    n = len(I.BE)
    B = [I.BA] + list(I.BE)
    mu = [I.BA[0] * I.lam[0] + I.BA[1] * I.lam[1] + I.alpha] + \
         [b[0] * I.lam[0] + b[1] * I.lam[1] - c for b, c in zip(I.BE, I.cE)]
    sizes = list(I.sf) + [I.sA] + list(I.sE)
    scen = list(itertools.product((-1, 1), repeat=len(sizes)))
    q, d = Fr(1, len(scen)), 1 + n
    Sig = [[Fr(0)] * d for _ in range(d)]
    ok = True
    for sg in scen:
        z = [s * x for s, x in zip(sg, sizes)]
        xi = [B[i][0] * z[0] + B[i][1] * z[1] + z[2 + i] for i in range(d)]
        for i in range(d):
            ok = ok and 1 + mu[i] + xi[i] > 0
            for j in range(d):
                Sig[i][j] += q * xi[i] * xi[j]
    return mu, Sig, ok


def cost(I, w):
    return sum(I.kbuy[i] * max(w[i] - I.w0[i], 0) + I.ksell[i] * max(I.w0[i] - w[i], 0) for i in range(len(w)))


def Q(I, mu, Sig, w):
    d = len(w)
    return (sum(mu[i] * w[i] for i in range(d))
            - I.gamma / 2 * sum(w[i] * Sig[i][j] * w[j] for i in range(d) for j in range(d)) - cost(I, w))


def slack(I, w):
    return I.k0 - sum(w[i] - I.w0[i] for i in range(len(w))) - cost(I, w)


def certified(I, mu, Sig, w, cls):
    d = len(w)
    if not (all(0 <= w[i] <= I.wbar[i] for i in range(d)) and slack(I, w) >= 0 and (cls != "E" or w[0] == I.w0[0])):
        return False
    g = [mu[i] - I.gamma * sum(Sig[i][j] * w[j] for j in range(d)) for i in range(d)]
    lo, hi = Fr(0), (None if slack(I, w) == 0 else Fr(0))
    for i in range(d):
        if cls == "E" and i == 0:
            continue
        if w[i] > I.w0[i]:
            zmin = zmax = I.kbuy[i]
        elif w[i] < I.w0[i]:
            zmin = zmax = -I.ksell[i]
        else:
            zmin, zmax = -I.ksell[i], I.kbuy[i]
        if w[i] != 0:
            ub = (g[i] - zmin) / (1 + zmin)
            hi = ub if hi is None else min(hi, ub)
        if w[i] != I.wbar[i]:
            lo = max(lo, (g[i] - zmax) / (1 + zmax))
    return hi is None or lo <= hi


def part_k():
    rows, bad = [], 0
    for geom, cst, al, g, sA, st in itertools.product(GEOM, COSTS, ALPHA, GAMMA, SA, STARTS):
        I = cell(geom, cst, al, g, sA, st)
        mu, Sig, ok = red_model(I)
        wF, wE = list(solve(I, "F", exact=True)[1]), list(solve(I, "E", exact=True)[1])
        if not (ok and certified(I, mu, Sig, wF, "F") and certified(I, mu, Sig, wE, "E")):
            bad += 1
        G = Q(I, mu, Sig, wF) - Q(I, mu, Sig, wE)
        rows.append((geom, cst, al, g, sA, st, G, wF[0] != I.w0[0], wF))
    print(f"Part K: {len(rows)} cells; not certified: {bad}")
    print("| Geometry | Costs | Cells | G*>0 | G*>=1bp | Median | Max | F trades active |")
    for geom, cst in itertools.product(GEOM, COSTS):
        r = [x for x in rows if x[0] == geom and x[1] == cst]
        Gs = [float(x[6] / BP) for x in r]
        print(f"| {geom} | {cst} | {len(r)} | {sum(x[6] > 0 for x in r)} | {sum(x[6] >= BP for x in r)} | "
              f"{median(Gs):.3f} | {max(Gs):.3f} | {sum(x[7] for x in r)} |")
    print("\nMedian G* by alpha (bp): geometry, alpha, Z, EQ5, ETFC5, ETF-stress")
    for geom, al in itertools.product(GEOM, ALPHA):
        med = [median(float(x[6] / BP) for x in rows if x[0] == geom and x[2] == al and x[1] == c)
               for c in ("Z", "EQ5", "ETFC5", "ETF-stress")]
        print(f"  {geom} {int(al)}: " + ", ".join(f"{m:.3f}" for m in med))
    g1 = sorted((x for x in rows if x[0] == "G1-exact" and x[1] == "Z" and x[2] == 0), key=lambda x: -x[6])
    print("\nH_K clause 2 (G1-exact, Z, alpha = 0; 12 cells): G* >= 1 bp in",
          sum(x[6] >= BP for x in g1), "cells:",
          [(f"{float(x[6] / BP):.3f} bp", f"gamma={x[3]}", f"sA={x[4]}", x[5], f"a*={float(x[8][0]):.3f}",
            f"total={float(sum(x[8])):.3f}") for x in g1 if x[6] >= BP])
    print("  S2 cells max G* (bp):", max(float(x[6] / BP) for x in g1 if x[5] == "S2"))
    stress = [x for x in rows if x[1] == "ETF-stress" and len(x[8]) == 3]
    print("ETF-stress: any F optimum holding E2:", any(x[8][2] > 0 for x in stress))
    return rows


def m_cell(args):
    geom, cst, al = args
    out = []
    I = cell(geom, cst, al, Fr(5), Fr(1, 50), "S1")
    mu, Sig, _ = red_model(I)
    VF = Q(I, mu, Sig, list(solve(I, "F", exact=True)[1]))
    VE = Q(I, mu, Sig, list(solve(I, "E", exact=True)[1]))
    Gstar = float((VF - VE) / BP)
    muf = [float(x) for x in mu]
    Sf = np.array([[float(x) for x in r] for r in Sig])
    If = replace(I, lam=tuple(float(x) for x in I.lam), alpha=float(I.alpha))

    def Qtrue(w):
        w = np.array([float(x) for x in w])
        c = sum(float(I.kbuy[i]) * max(w[i] - float(I.w0[i]), 0) + float(I.ksell[i]) * max(float(I.w0[i]) - w[i], 0)
                for i in range(len(w)))
        return float(np.dot(muf, w) - float(I.gamma) / 2 * w @ Sf @ w - c)

    for info, T in itertools.product(["L", "A", "LA"], [40, 160]):
        D, reg = [], {1: [], 2: [], 3: []}
        for r in range(2000):
            rng = np.random.default_rng((7006, T, r))
            bf = rng.binomial(T, 0.5, size=2)
            bA = rng.binomial(T, 0.5)
            lam_hat = tuple(float(I.lam[k]) + float(I.sf[k]) * (2 * bf[k] - T) / T for k in range(2))
            al_hat = float(I.alpha) + float(I.sA) * (2 * bA - T) / T
            lam_p = lam_hat if "L" in info else tuple(float(x) for x in I.lam)
            al_p = al_hat if "A" in info else float(I.alpha)
            J = replace(If, lam=lam_p, alpha=al_p)
            w1 = solve(J, "E", exact=False)[1]
            w2 = solve(J, "F", exact=False)[1]
            w3 = solve(replace(J, alpha=al_p * T / (T + 40)), "F", exact=False)[1] if "A" in info else w2
            q1, q2, q3 = Qtrue(w1), Qtrue(w2), Qtrue(w3)
            D.append((q2 - q1) * 1e4)
            for k, qq in ((1, q1), (2, q2), (3, q3)):
                reg[k].append((float(VF) - qq) * 1e4)
        D = np.array(D)
        m, se = D.mean(), D.std(ddof=1) / np.sqrt(len(D))
        out.append((geom, cst, int(al), info, T, Gstar, m, se, [np.mean(reg[k]) for k in (1, 2, 3)]))
    return out


def part_m():
    from multiprocessing import Pool
    jobs = list(itertools.product(GEOM, ["Z", "EQ5", "ETFC5"], [Fr(-25), Fr(0), Fr(25)]))
    with Pool(8) as pool:
        out = [o for res in pool.map(m_cell, jobs) for o in res]
    for o in out:
        print(f"{o[0]} {o[1]} {o[2]} {o[3]} {o[4]}: G*={o[5]:.3f} D={o[6]:.3f} ({o[7]:.3f}) "
              f"regret P1-P3 = {', '.join(f'{x:.3f}' for x in o[8])}")
    pos = [o for o in out if o[5] > 1e-12]
    rev = sum(o[6] + 2 * o[7] < 0 for o in pos)
    conf = sum(o[6] - 2 * o[7] > 0 for o in pos)
    print(f"\nPart M: cells with G* > 0: {len(pos)}; D significantly negative: {rev}; significantly positive: {conf}")
    for info, T in itertools.product(["L", "A", "LA"], [40, 160]):
        s = [o for o in pos if o[3] == info and o[4] == T]
        print(f"  {info} T={T}: {sum(o[6] + 2 * o[7] < 0 for o in s)} reversed, {sum(o[6] - 2 * o[7] > 0 for o in s)} confirmed (of {len(s)})")
    big = [o for o in out if o[5] >= 1]
    print(f"Restricted to cells with G* >= 1 bp: {len(big)} cells; reversed {sum(o[6] + 2 * o[7] < 0 for o in big)}, "
          f"confirmed {sum(o[6] - 2 * o[7] > 0 for o in big)}")
    return out


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "KM"
    if "K" in which:
        part_k()
    if "M" in which:
        part_m()
