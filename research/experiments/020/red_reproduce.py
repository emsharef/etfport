"""Red's reproduction of experiment 020, written from the registered Design without reading run.py.

Part X (exact): 018's 2S-alpha design on the Design's subset, with red's cross-moment covariance
Sigma_ij = B_i Sf B_j' + B_i c_j + B_j c_i + D_ij (c_i = Cov(f, z_i)). The experiment 004 exact solver is
run with its covariance routine patched to this Sigma (as registered), every optimum is certified by
red's own exact KKT certificate with the same Sigma, stage 1 is red's exact hull maximization, and
stage 2 is the M2 instance with lambda replaced by gamma Sf b* (valid for any Sigma). V is evaluated
exactly on the 21 x 21 grid by red's own exact maximization of Q over each fibre (a point with one ETF, a
segment with two: endpoints, cost kinks, funding roots and stationary points of each piece).
Part R: the registered rule family, brute-forced on red's own experiment 018 gaps (720 cells).

Usage: uv run python experiments/020/red_reproduce.py
"""
import importlib.util
import itertools
from dataclasses import replace
from fractions import Fraction as Fr
from multiprocessing import Pool
from pathlib import Path
from statistics import median

HERE = Path(__file__).resolve().parent
def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
R18 = load("red018", HERE.parent / "018" / "red_reproduce.py")
R6 = R18.R6
import m2  # noqa: E402

BP = Fr(1, 10000)
LEVELS = {"L0": (0, 0, 0), "L1": (0, Fr(1, 5), 0), "L2": (0, Fr(2, 5), 0), "L3": (0, Fr(-1, 5), 0), "L4": (Fr(1, 5), 0, Fr(1, 5))}
SF = R6.SF


def sigma_cross(I, lev):
    rAM, rAH, rEM = LEVELS[lev]
    B = [I.BA] + list(I.BE)
    sd = [I.sA] + list(I.sE)
    c = [(rAM * SF[0] * I.sA, rAH * SF[1] * I.sA)] + [(rEM * SF[0] * s, Fr(0)) for s in I.sE]
    Sf = [[SF[0] ** 2, 0], [0, SF[1] ** 2]]
    d = len(B)
    S = [[sum(B[i][k] * Sf[k][l] * B[j][l] for k in range(2) for l in range(2))
          + sum(B[i][k] * c[j][k] for k in range(2)) + sum(B[j][k] * c[i][k] for k in range(2))
          + (sd[i] ** 2 if i == j else 0) for j in range(d)] for i in range(d)]
    # joint covariance of (f1, f2, z_1..z_d) must be positive definite: exact leading minors
    J = [[Sf[0][0], 0] + [c[j][0] for j in range(d)], [0, Sf[1][1]] + [c[j][1] for j in range(d)]]
    J += [[c[i][0], c[i][1]] + [(sd[i] ** 2 if i == j else 0) for j in range(d)] for i in range(d)]
    pd = all(det([r[:k] for r in J[:k]]) > 0 for k in range(1, len(J) + 1))
    return S, pd


def det(M):
    M = [r[:] for r in M]; n = len(M); dt = Fr(1)
    for i in range(n):
        p = next((r for r in range(i, n) if M[r][i] != 0), None)
        if p is None:
            return Fr(0)
        if p != i:
            M[i], M[p] = M[p], M[i]; dt = -dt
        dt *= M[i][i]
        for r in range(i + 1, n):
            f = M[r][i] / M[i][i]
            M[r] = [a - f * b for a, b in zip(M[r], M[i])]
    return dt


def solve_with(I, S, cls="F"):
    m2.sigma_formula = lambda _I: S
    return m2.solve(I, cls)


def Qv(I, mu, S, w):
    return R6.Q(I, mu, S, w)


def fibre_max(I, mu, S, b):
    """Exact max of Q over {w in F : B'w = b}, or None if the fibre is empty."""
    B = [I.BA] + list(I.BE); d = len(B)
    if d == 2:
        det2 = B[0][0] * B[1][1] - B[0][1] * B[1][0]
        a = (b[0] * B[1][1] - b[1] * B[1][0]) / det2; p = (B[0][0] * b[1] - B[0][1] * b[0]) / det2
        w = [a, p]
        return Qv(I, mu, S, w) if feas(I, w) else None
    # d = 3: particular solution with w[1] free and null direction
    M = [[B[i][k] for i in range(3)] for k in range(2)]           # 2 x 3, columns = instruments
    # null direction n: cross product of the two rows
    n = [M[0][1] * M[1][2] - M[0][2] * M[1][1], M[0][2] * M[1][0] - M[0][0] * M[1][2], M[0][0] * M[1][1] - M[0][1] * M[1][0]]
    # particular solution: set the coordinate with largest |n| to 0 and solve the 2 x 2
    k = max(range(3), key=lambda i: abs(n[i])); idx = [i for i in range(3) if i != k]
    a11, a12, a21, a22 = M[0][idx[0]], M[0][idx[1]], M[1][idx[0]], M[1][idx[1]]
    dd = a11 * a22 - a12 * a21
    x = [Fr(0)] * 3
    x[idx[0]] = (b[0] * a22 - a12 * b[1]) / dd; x[idx[1]] = (a11 * b[1] - a21 * b[0]) / dd
    w = lambda t: [x[i] + t * n[i] for i in range(3)]
    cands = set()
    for i in range(3):
        if n[i] != 0:
            for v in (Fr(0), Fr(1), I.w0[i]):
                cands.add((v - x[i]) / n[i])
    cands = sorted(cands)
    # funding roots on each piece between consecutive candidates, and stationary points
    extra = set()
    pts = cands
    for lo, hi in zip(pts, pts[1:]):
        mid = (lo + hi) / 2
        wm = w(mid)
        s = [1 if wm[i] > I.w0[i] else -1 if wm[i] < I.w0[i] else 0 for i in range(3)]
        rate = [I.kbuy[i] if s[i] > 0 else I.ksell[i] if s[i] < 0 else 0 for i in range(3)]
        # funding k0 - sum (1 + rate_i s_i)(w_i - w0_i) = 0, linear in t
        c0 = I.k0 - sum((1 + rate[i] * s[i]) * (x[i] - I.w0[i]) for i in range(3))
        c1 = -sum((1 + rate[i] * s[i]) * n[i] for i in range(3))
        if c1 != 0:
            t = -c0 / c1
            if lo <= t <= hi:
                extra.add(t)
        # stationary point of mu'w - rate s'(w - w0) - (g/2) w'Sw along t
        lin = sum((mu[i] - rate[i] * s[i]) * n[i] for i in range(3)) - I.gamma * sum(x[i] * S[i][j] * n[j] for i in range(3) for j in range(3))
        quad = I.gamma * sum(n[i] * S[i][j] * n[j] for i in range(3) for j in range(3))
        if quad != 0:
            t = lin / quad
            if lo <= t <= hi:
                extra.add(t)
    best = None
    for t in set(cands) | extra:
        ww = w(t)
        if feas(I, ww):
            q = Qv(I, mu, S, ww)
            if best is None or q > best:
                best = q
    return best


def feas(I, w):
    return all(0 <= w[i] <= I.wbar[i] for i in range(len(w))) and R6.slack(I, w) >= 0


def x_cell(args):
    geom, rates, al, g, lev = args
    I = R6.cell(geom, "Z", al, g, Fr(1, 50), "S1")
    (ab, as_), (eb, es) = R18.RATES[rates]
    n = len(I.BE)
    I = replace(I, kbuy=(ab * BP,) + (eb * BP,) * n, ksell=(as_ * BP,) + (es * BP,) * n)
    S, pd = sigma_cross(I, lev)
    mu = m2.mean_vector(I)
    _, wJ, _ = solve_with(I, S)
    assert R6.certified(I, mu, S, wJ, "F")
    B = [I.BA] + list(I.BE)
    bstar, _ = R18.stage1([(Fr(0), Fr(0))] + B, I.lam, g)
    J = replace(I, lam=(g * R18.SF2[0] * bstar[0], g * R18.SF2[1] * bstar[1]))
    mu2 = m2.mean_vector(J)
    _, w2, cands = solve_with(J, S)
    assert R6.certified(J, mu2, S, w2, "F")
    gap = (Qv(I, mu, S, wJ) - Qv(I, mu, S, w2)) / BP
    nu = (I.lam[0] - g * R18.SF2[0] * bstar[0], I.lam[1] - g * R18.SF2[1] * bstar[1])
    de = [sum((wJ[i] - w2[i]) * B[i][k] for i in range(len(B))) for k in range(2)]
    lin = (nu[0] * de[0] + nu[1] * de[1]) / BP
    # V on the grid
    G = lambda b: I.lam[0] * b[0] + I.lam[1] * b[1] - g / 2 * (R18.SF2[0] * b[0] ** 2 + R18.SF2[1] * b[1] ** 2)
    V = {}
    for i in range(21):
        for j in range(21):
            b = (Fr(i, 20), Fr(3 * j, 200))
            q = fibre_max(I, mu, S, b)
            if q is not None:
                V[(i, j)] = q - G(b)
    worst = Fr(0)
    for (i, j), v in V.items():
        for di, dj in ((1, 0), (0, 1), (1, 1), (1, -1)):
            p, m = (i + di, j + dj), (i - di, j - dj)
            if p in V and m in V:
                worst = min(worst, v - (V[p] + V[m]) / 2)
    return dict(geom=geom, rates=rates, al=int(al), g=int(g), lev=lev, pd=pd, gap=gap, lin=lin, unique=len(cands) == 1,
                Jb=any(x == 0 or x == 1 for x in wJ), Jf=R6.slack(I, wJ) == 0, worst=worst / BP, npts=len(V))


def part_x():
    grid = [(geom, r, al, g, lev) for lev in LEVELS for geom in R6.GEOM for r in ("Z", "FL-554")
            for al in (Fr(-25), Fr(0), Fr(25)) for g in R6.GAMMA]
    with Pool(8) as p:
        res = p.map(x_cell, grid)
    f = float
    print(f"cells {len(res)}; joint covariance PD in {sum(r['pd'] for r in res)}; stage-2 unique in {sum(r['unique'] for r in res)}")
    print("| level | cells | gap 0 | < 1 | >= 1 | median | max | gap <= nu'De | V concave on grid | worst violation (bp) |")
    for lev in LEVELS:
        rs = [r for r in res if r["lev"] == lev]; gs = [r["gap"] for r in rs]
        print(f"| {lev} | {len(rs)} | {sum(x == 0 for x in gs)} | {sum(x < 1 for x in gs)} | {sum(x >= 1 for x in gs)} | "
              f"{f(median(gs)):.3f} | {f(max(gs)):.3f} | {sum(r['gap'] <= r['lin'] for r in rs)} | {sum(r['worst'] >= 0 for r in rs)} | {f(min(r['worst'] for r in rs)):.4f} |")
    base = {(r["geom"], r["rates"], r["al"], r["g"]): r["gap"] for r in res if r["lev"] == "L0"}
    for lev in ("L1", "L2", "L3", "L4"):
        ch = [r["gap"] - base[(r["geom"], r["rates"], r["al"], r["g"])] for r in res if r["lev"] == lev]
        print(f"  {lev}: change vs L0 median {f(median(ch)):.3f}, range {f(min(ch)):.2f} to {f(max(ch)):.2f}, up >= 1: {sum(c >= 1 for c in ch)}, down <= -1: {sum(c <= -1 for c in ch)}")
        viol = [r for r in res if r["lev"] == lev and r["worst"] < 0]
        print(f"      non-concave cells by geometry: { {gm: sum(r['geom'] == gm for r in viol) for gm in R6.GEOM} }")
    big = [r for r in res if r["gap"] >= 1]
    print(f"  gap >= 1 bp: {len(big)}; joint on a long-only or cap bound {sum(r['Jb'] for r in big)}; funding tight {sum(r['Jf'] for r in big)}")
    return res


def conditions():
    cs = []
    for a in R6.ALPHA:
        cs += [(f"alpha >= {a}", lambda r, a=a: r["al"] >= a), (f"alpha <= {a}", lambda r, a=a: r["al"] <= a)]
    for rt in R18.RATES:
        cs.append((f"rates = {rt}", lambda r, rt=rt: r["rates"] == rt))
    for g in R6.GAMMA:
        cs += [(f"gamma >= {g}", lambda r, g=g: r["g"] >= g), (f"gamma <= {g}", lambda r, g=g: r["g"] <= g)]
    for gm in R6.GEOM:
        cs.append((f"geometry = {gm}", lambda r, gm=gm: r["geom"] == gm))
    for st in R6.STARTS:
        cs.append((f"start = {st}", lambda r, st=st: r["start"] == st))
    return cs


def r18_one(args):
    return R18.one(args)


def part_r(xres):
    grid = [(geom, r, al, g, sA, st) for geom in R6.GEOM for r in R18.RATES for al in R6.ALPHA for g in R6.GAMMA
            for sA in R6.SA for st in R6.STARTS]
    with Pool(8) as p:
        res = p.map(r18_one, grid)
    rows = [dict(al=r["alpha"], rates=r["rates"], g=r["gamma"], geom=r["geom"], start=r["start"], safe=r["gap_alpha"] < 1) for r in res]
    cs = conditions()
    rules = [((n,), f) for n, f in cs]
    for (n1, f1), (n2, f2) in itertools.combinations(cs, 2):
        rules.append(((n1, "AND", n2), lambda r, f1=f1, f2=f2: f1(r) and f2(r)))
        rules.append(((n1, "OR", n2), lambda r, f1=f1, f2=f2: f1(r) or f2(r)))
    def score(f, rs):
        acc = sum(f(r) == r["safe"] for r in rs); fs = sum(f(r) and not r["safe"] for r in rs); ns = sum(f(r) for r in rs)
        return acc, fs, ns
    scored = [(score(f, rows), name, f) for name, f in rules]
    best = max(scored, key=lambda s: (s[0][0], -s[0][1], -len(s[1])))
    single = max((s for s in scored if len(s[1]) == 1), key=lambda s: (s[0][0], -s[0][1]))
    ties = [s[1] for s in scored if s[0][0] == best[0][0] and s[0][1] == best[0][1] and len(s[1]) == len(best[1])]
    print(f"Part R: base rate safe {sum(r['safe'] for r in rows)} of 720")
    print(f"  best rule {' '.join(best[1])}: accuracy {best[0][0]}/720, safe calls {best[0][2]}, false-safe {best[0][1]}; ties at this score: {len(ties)} {ties[:4]}")
    print(f"  best single {' '.join(single[1])}: accuracy {single[0][0]}, false-safe {single[0][1]}")
    xr = [dict(al=r["al"], rates=r["rates"], g=r["g"], geom=r["geom"], start="S1", safe=r["gap"] < 1, lev=r["lev"]) for r in xres]
    acc, fs, _ = score(best[2], xr)
    print(f"  out of sample on Part X: accuracy {acc}/270, false-safe {fs}; by level " +
          ", ".join(f"{lev} {score(best[2], [r for r in xr if r['lev'] == lev])[:2]}" for lev in LEVELS))


if __name__ == "__main__":
    xres = part_x()
    part_r(xres)
