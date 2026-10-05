"""Red's reproduction of experiment 019, written from the registered Design without reading run.py.

Part S (exact): on experiment 018's 720 cells, red's experiment 018 driver (exact stage 1, stage 2 as an
M2 instance, KKT-certified optima) supplies w_J and w_2S; red computes nu = lambda - gamma Sf b*,
Delta e = B'w_J - B'w_2S, Delta w, the exact quadratic term and the scaling ratios.
Part E (Monte Carlo): experiment 006 Part M's grid and estimation law, with red's own independent draws
(numpy default_rng seeded by (9019, T, r), not the analyst's (2006, T, r)), so agreement is statistical.
Policies: 2S (stage 1 over conv{0, loading rows} with estimated premia and known Sf; stage 2 the M2
problem with mean gamma B Sf b* + alpha-hat e_A - c^E), JP (full-trading plug-in), EP (ETF-only plug-in),
all float-mode M2 solves, evaluated with the true score.

Usage: uv run python experiments/019/red_reproduce.py [S|E]
"""
import importlib.util
import itertools
import sys
from dataclasses import replace
from fractions import Fraction as Fr
from multiprocessing import Pool
from pathlib import Path
from statistics import median

import numpy as np

HERE = Path(__file__).resolve().parent
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
R18 = load("red018", HERE.parent / "018" / "red_reproduce.py")
R6 = R18.R6
from m2 import solve  # noqa: E402

BP = Fr(1, 10000)
SF2 = [float(x) for x in R18.SF2]


def s_cell(args):
    geom, rates, al, g, sA, st = args
    I = R6.cell(geom, "Z", al, g, sA, st)
    (ab, as_), (eb, es) = R18.RATES[rates]
    n = len(I.BE)
    I = replace(I, kbuy=(ab * BP,) + (eb * BP,) * n, ksell=(as_ * BP,) + (es * BP,) * n)
    mu, Sig, _ = R6.red_model(I)
    _, wJ, _ = solve(I, "F")
    B = [I.BA] + list(I.BE)
    bstar, _ = R18.stage1([(Fr(0), Fr(0))] + B, I.lam, g)
    J = replace(I, lam=(g * R18.SF2[0] * bstar[0], g * R18.SF2[1] * bstar[1]))
    _, w2, _ = solve(J, "F")
    gap = (R6.Q(I, mu, Sig, wJ) - R6.Q(I, mu, Sig, w2)) / BP
    nu = (I.lam[0] - g * R18.SF2[0] * bstar[0], I.lam[1] - g * R18.SF2[1] * bstar[1])
    eJ = [sum(wJ[i] * B[i][k] for i in range(len(B))) for k in range(2)]
    e2 = [sum(w2[i] * B[i][k] for i in range(len(B))) for k in range(2)]
    de = [eJ[k] - e2[k] for k in range(2)]
    dw = [wJ[i] - w2[i] for i in range(len(wJ))]
    lin = (nu[0] * de[0] + nu[1] * de[1]) / BP
    quad = g / 2 * sum(dw[i] * Sig[i][j] * dw[j] for i in range(len(dw)) for j in range(len(dw))) / BP
    slack2 = dict(fund=R6.slack(I, w2), lo=min(w2), cap=min(1 - x for x in w2))
    return dict(gap=gap, lin=lin, quad=quad, nu=(float(nu[0]), float(nu[1])), de=(float(de[0]), float(de[1])),
                slack=tuple(float(v) for v in slack2.values()))


def part_s():
    grid = [(geom, r, al, g, sA, st) for geom in R6.GEOM for r in R18.RATES for al in R6.ALPHA for g in R6.GAMMA
            for sA in R6.SA for st in R6.STARTS]
    with Pool(8) as p:
        res = p.map(s_cell, grid)
    pos = [r for r in res if r["gap"] > 0]
    print(f"cells {len(res)}, gap > 0: {len(pos)}")
    print(f"gap <= nu'De in {sum(r['gap'] <= r['lin'] for r in res)}; gap == nu'De - quad exactly in {sum(r['gap'] == r['lin'] - r['quad'] for r in res)}")
    z = [r for r in res if r["gap"] == 0]
    print(f"zero-gap cells {len(z)}, of which De = 0: {sum(r['de'] == (0.0, 0.0) for r in z)}; De = 0 among gap > 0: {sum(r['de'] == (0.0, 0.0) for r in pos)}")
    nn = lambda v: float(np.hypot(*v))
    rat = {"gap/nu'De": [float(r["gap"] / r["lin"]) for r in pos],
           "gap/(|nu||De|)": [float(r["gap"]) / (nn(r["nu"]) * nn(r["de"]) * 1e4) for r in pos],
           "gap/quad": [float(r["gap"] / r["quad"]) if r["quad"] > 0 else float("inf") for r in pos]}
    for k, v in rat.items():
        print(f"  {k:16s} min {min(v):.3f} median {median(v):.3f} max {max(v):.3f}")
    x1 = np.log([nn(r["de"]) for r in pos]); x2 = np.log([nn(r["nu"]) * nn(r["de"]) for r in pos]); y = np.log([float(r["gap"]) for r in pos])
    print(f"  log-log slope on |De| {np.polyfit(x1, y, 1)[0]:.3f}; on |nu||De| {np.polyfit(x2, y, 1)[0]:.3f}")
    allnu = [nn(r["nu"]) for r in res]
    print(f"  |nu| range {min(allnu):.5f}-{max(allnu):.5f}")
    for lab, rs in (("gap = 0", z), ("gap > 0", pos)):
        print(f"  slack at 2S, {lab}: funding {median([r['slack'][0] for r in rs]):.2f}, long-only {median([r['slack'][1] for r in rs]):.2f}, cap {median([r['slack'][2] for r in rs]):.2f}")


def stage1_float(pts, lam, g):
    bu = (lam[0] / (g * SF2[0]), lam[1] / (g * SF2[1]))
    Gf = lambda b: lam[0] * b[0] + lam[1] * b[1] - g / 2 * (SF2[0] * b[0] ** 2 + SF2[1] * b[1] ** 2)
    rows = pts[1:]
    for i, j in itertools.combinations(range(len(rows)), 2):
        r, s = rows[i], rows[j]
        det = r[0] * s[1] - r[1] * s[0]
        if abs(det) > 1e-15:
            t = (bu[0] * s[1] - bu[1] * s[0]) / det; u = (r[0] * bu[1] - r[1] * bu[0]) / det
            if t >= 0 and u >= 0 and t + u <= 1:
                return bu
    best, arg = None, None
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            p, q = pts[i], pts[j]
            d = (q[0] - p[0], q[1] - p[1])
            grad = (lam[0] - g * SF2[0] * p[0], lam[1] - g * SF2[1] * p[1])
            den = g * (SF2[0] * d[0] ** 2 + SF2[1] * d[1] ** 2)
            t = min(max((grad[0] * d[0] + grad[1] * d[1]) / den, 0.0), 1.0) if den else 0.0
            b = (p[0] + t * d[0], p[1] + t * d[1]); v = Gf(b)
            if best is None or v > best:
                best, arg = v, b
    return arg


def e_cell(args):
    geom, cst, al = args
    I = R6.cell(geom, cst, al, Fr(5), Fr(1, 50), "S1")
    mu, Sig, _ = R6.red_model(I)
    VF = float(R6.Q(I, mu, Sig, list(solve(I, "F", exact=True)[1])))
    muf = np.array([float(x) for x in mu]); Sf = np.array([[float(x) for x in r] for r in Sig])
    kb = np.array([float(x) for x in I.kbuy]); ks = np.array([float(x) for x in I.ksell]); w0 = np.array([float(x) for x in I.w0])
    g = float(I.gamma)
    def Qt(w):
        w = np.array([float(x) for x in w])
        return float(muf @ w - g / 2 * w @ Sf @ w - kb @ np.maximum(w - w0, 0) - ks @ np.maximum(w0 - w, 0))
    If = replace(I, lam=tuple(float(x) for x in I.lam), alpha=float(I.alpha), cE=tuple(float(x) for x in I.cE),
                 kbuy=tuple(kb), ksell=tuple(ks), sf=tuple(float(x) for x in I.sf), sA=float(I.sA),
                 sE=tuple(float(x) for x in I.sE), gamma=g, w0=tuple(w0), k0=float(I.k0), wbar=tuple(float(x) for x in I.wbar),
                 BA=tuple(float(x) for x in I.BA), BE=tuple(tuple(float(y) for y in b) for b in I.BE))
    pts = [(0.0, 0.0)] + [tuple(float(y) for y in b) for b in [I.BA] + list(I.BE)]
    out = []
    for info, T in itertools.product(["L", "A", "LA"], [40, 160]):
        D, reg = [], {"2S": [], "JP": [], "EP": []}
        for r in range(2000):
            rng = np.random.default_rng((9019, T, r))
            bf = rng.binomial(T, 0.5, size=2); bA = rng.binomial(T, 0.5)
            lam_hat = tuple(float(I.lam[k]) + float(I.sf[k]) * (2 * bf[k] - T) / T for k in range(2))
            al_hat = float(I.alpha) + float(I.sA) * (2 * bA - T) / T
            lam_p = lam_hat if "L" in info else tuple(float(x) for x in I.lam)
            al_p = al_hat if "A" in info else float(I.alpha)
            J = replace(If, lam=lam_p, alpha=al_p)
            wJP = solve(J, "F", exact=False)[1]; wEP = solve(J, "E", exact=False)[1]
            b = stage1_float(pts, lam_p, g)
            w2 = solve(replace(J, lam=(g * SF2[0] * b[0], g * SF2[1] * b[1])), "F", exact=False)[1]
            q2, qJ, qE = Qt(w2), Qt(wJP), Qt(wEP)
            D.append((q2 - qJ) * 1e4)
            for k, q in (("2S", q2), ("JP", qJ), ("EP", qE)):
                reg[k].append((VF - q) * 1e4)
        D = np.array(D)
        out.append(dict(geom=geom, cst=cst, al=int(al), info=info, T=T, D=D.mean(), se=D.std(ddof=1) / np.sqrt(len(D)),
                        reg={k: float(np.mean(v)) for k, v in reg.items()}, pties=float(np.mean(np.abs(D) <= 1e-8))))
    return out


def part_e():
    jobs = list(itertools.product(R6.GEOM, ["Z", "EQ5", "ETFC5"], [Fr(-25), Fr(0), Fr(25)]))
    with Pool(8) as p:
        out = [o for res in p.map(e_cell, jobs) for o in res]
    v = ["2S better" if o["D"] - 2 * o["se"] > 0 else "JP better" if o["D"] + 2 * o["se"] < 0 else "tie" for o in out]
    for o, vv in zip(out, v):
        o["v"] = vv
    print(f"cells {len(out)}: JP better {v.count('JP better')}, 2S better {v.count('2S better')}, tie {v.count('tie')}; "
          f"D range {min(o['D'] for o in out):.2f} to {max(o['D'] for o in out):.2f}; SE > 0.1 in {sum(o['se'] > 0.1 for o in out)} (max {max(o['se'] for o in out):.3f})")
    sl = {"all": out, "alpha -25": [o for o in out if o["al"] == -25], "alpha 0": [o for o in out if o["al"] == 0],
          "alpha +25": [o for o in out if o["al"] == 25], "A only": [o for o in out if o["info"] == "A"],
          "L only": [o for o in out if o["info"] == "L"], "LA": [o for o in out if o["info"] == "LA"],
          "T=40": [o for o in out if o["T"] == 40], "T=160": [o for o in out if o["T"] == 160], "rates Z": [o for o in out if o["cst"] == "Z"]}
    for k, s in sl.items():
        print(f"  {k:10s} median regret 2S {median(o['reg']['2S'] for o in s):6.2f} JP {median(o['reg']['JP'] for o in s):6.2f} EP {median(o['reg']['EP'] for o in s):6.2f}")
    for lab, s in (("alpha -25", sl["alpha -25"]), ("L only", sl["L only"]), ("T=40", sl["T=40"])):
        print(f"  2S better in {lab}: {sum(o['v'] == '2S better' for o in s)} of {len(s)}, median D {median(o['D'] for o in s):+.2f}")
    for lab, s in (("alpha 0", sl["alpha 0"]), ("A only", sl["A only"]), ("nonzero rates", [o for o in out if o["cst"] != "Z"])):
        print(f"  JP better in {lab}: {sum(o['v'] == 'JP better' for o in s)} of {len(s)}, median D {median(o['D'] for o in s):+.2f}")
    print(f"  2S ties or beats JP: {sum(o['v'] != 'JP better' for o in out)} of {len(out)}")
    import json
    json.dump(out, open(HERE / "red_partE.json", "w"), default=float)


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "SE"
    if "S" in which:
        part_s()
    if "E" in which:
        part_e()
