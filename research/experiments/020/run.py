"""Experiment 020 (D4): cross-moment sensitivity of experiment 018's two-stage gap, concavity of claim 027's residual
value V, and an observable safe-condition rule from 018's outputs.
Registered design: experiments/020-m2-cross-moments.md.

M2's covariance with residual-factor cross moments: for instruments i, j with loading rows B_i and factor-residual
covariance vectors c_i = Cov(f, z_i) (2-vectors),
    Sigma_ij = B_i Sf B_j' + B_i c_j + B_j c_i + D_ij,
with c_A = (rho_A1 sf_1 sA, rho_A2 sf_2 sA), c_E = (rho_E1 sf_1 sE, 0). M2's score uses only the mean and this
covariance. The exact solver of experiments/004/m2.py is used with its covariance routine patched for these
instances (its enumeration uses whatever Sigma it is given). Everything is exact rational arithmetic.

Run:    uv run python experiments/020/run.py          (writes experiments/020/results.json)
Report: uv run python experiments/020/run.py report
"""

import importlib.util
import itertools
import json
import os
import sys
import time
from dataclasses import dataclass
from fractions import Fraction as Fr
from multiprocessing import Pool
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


e018 = _load("e018", ROOT / "experiments" / "018" / "run.py")
import m2  # noqa: E402  (path set by e018)

_orig_sigma = m2.sigma_formula


@dataclass(frozen=True)
class XInstance(m2.Instance2):
    xc: tuple = ()          # factor-residual covariance vectors c_i, one 2-vector per instrument


def sigma_x(I):
    S = _orig_sigma(I)
    if not isinstance(I, XInstance) or not I.xc:
        return S
    rows = [I.BA] + list(I.BE)
    return [[S[i][j] + sum(rows[i][k] * I.xc[j][k] + rows[j][k] * I.xc[i][k] for k in range(2))
             for j in range(I.d)] for i in range(I.d)]


m2.sigma_formula = sigma_x          # m2.solve reads its module global

# ---- assumed cross-moment levels (correlations of residuals with factor shocks)
LEVELS = {
    "L0 none (006)": (Fr(0), Fr(0), Fr(0)),               # (rho_A,Mkt, rho_A,HML, rho_E,Mkt)
    "L1 active-HML +0.2": (Fr(0), Fr(1, 5), Fr(0)),
    "L2 active-HML +0.4": (Fr(0), Fr(2, 5), Fr(0)),
    "L3 active-HML -0.2": (Fr(0), Fr(-1, 5), Fr(0)),
    "L4 active-Mkt +0.2, ETF-Mkt +0.2": (Fr(1, 5), Fr(0), Fr(1, 5)),
}
GEOMS = list(e018.GEOMETRY)
COSTS = ["Z", "FL-554"]
ALPHAS = [Fr(-1, 400), Fr(0), Fr(1, 400)]
GAMMAS = [Fr(2), Fr(5), Fr(10)]
SA, START = Fr(1, 50), "S1-active-heavy"
GRID = 20                                   # V grid: b1 in [0,1], b2 in [0, 3/10], 21 x 21 points


def xinstance(geom, cost, alpha, gamma, level):
    I = e018.instance(geom, cost, alpha, gamma, SA, START)
    rA1, rA2, rE1 = LEVELS[level]
    xc = ((rA1 * e018.SF[0] * SA, rA2 * e018.SF[1] * SA),) + tuple((rE1 * e018.SF[0] * e018.SE_ETF, Fr(0)) for _ in I.BE)
    return XInstance(**{f: getattr(I, f) for f in I.__dataclass_fields__}, xc=xc)


def psd_ok(I):
    """The joint covariance of (f, z_A, z_E...) is positive semidefinite (Sylvester on leading minors, exact)."""
    n = 2 + I.d
    sd = [e018.SF[0], e018.SF[1], I.sA] + list(I.sE)
    M = [[Fr(0)] * n for _ in range(n)]
    M[0][0], M[1][1] = sd[0] ** 2, sd[1] ** 2
    for i in range(I.d):
        M[2 + i][2 + i] = sd[2 + i] ** 2
        for k in range(2):
            M[k][2 + i] = M[2 + i][k] = I.xc[i][k]

    def det(A):
        A = [r[:] for r in A]; m = len(A); d = Fr(1)
        for c in range(m):
            p = next((r for r in range(c, m) if A[r][c] != 0), None)
            if p is None:
                return Fr(0)
            if p != c:
                A[c], A[p] = A[p], A[c]; d = -d
            d *= A[c][c]
            for r in range(c + 1, m):
                f = A[r][c] / A[c][c]
                for k in range(c, m):
                    A[r][k] -= f * A[c][k]
        return d
    return all(det([r[:k] for r in M[:k]]) > 0 for k in range(1, n + 1))


def Qx(I, w):
    return m2.objective(I, sigma_x(I), m2.mean_vector(I), w)


def G(I, b):
    return sum(e018.LAM[k] * b[k] for k in range(2)) - I.gamma / 2 * sum(e018.SF[k] ** 2 * b[k] ** 2 for k in range(2))


def fibre_max(I, b):
    """V(b) + G(b) = max {Q(w) : w in F, B'w = b}, exact; None if the fibre is empty. d = 2: unique w. d = 3: a segment."""
    rows = [I.BA] + list(I.BE)
    d = I.d

    def feas(w):
        return m2.feasible(I, w)
    if d == 2:
        # solve [B_A B_E] (as columns) w = b
        a11, a12, a21, a22 = rows[0][0], rows[1][0], rows[0][1], rows[1][1]
        det = a11 * a22 - a12 * a21
        w = [(b[0] * a22 - a12 * b[1]) / det, (a11 * b[1] - a21 * b[0]) / det]
        return Qx(I, w) if feas(w) else None
    # d = 3: particular solution with w_E2 = 0 when possible, and null direction n
    import fractions  # noqa: F401
    Bt = [[rows[i][k] for i in range(3)] for k in range(2)]          # 2 x 3
    # null vector via cross product of the two rows
    n = [Bt[0][1] * Bt[1][2] - Bt[0][2] * Bt[1][1], Bt[0][2] * Bt[1][0] - Bt[0][0] * Bt[1][2],
         Bt[0][0] * Bt[1][1] - Bt[0][1] * Bt[1][0]]
    # particular: pick two columns with nonzero minor
    wp = None
    for i, j in ((0, 1), (0, 2), (1, 2)):
        det = Bt[0][i] * Bt[1][j] - Bt[0][j] * Bt[1][i]
        if det != 0:
            wp = [Fr(0)] * 3
            wp[i] = (b[0] * Bt[1][j] - Bt[0][j] * b[1]) / det
            wp[j] = (Bt[0][i] * b[1] - Bt[1][i] * b[0]) / det
            break
    # t-interval from 0 <= w <= wbar
    lo, hi = None, None
    for i in range(3):
        for bound in (Fr(0), I.wbar[i]):
            if n[i] == 0:
                if not (0 <= wp[i] <= I.wbar[i]):
                    return None
                continue
            t = (bound - wp[i]) / n[i]
            if (n[i] > 0) == (bound == 0):
                lo = t if lo is None or t > lo else lo
            else:
                hi = t if hi is None or t < hi else hi
    if lo is not None and hi is not None and lo > hi:
        return None
    # breakpoints of tau: v_i(t) = 0
    bps = sorted({(I.w0[i] - wp[i]) / n[i] for i in range(3) if n[i] != 0 and lo <= (I.w0[i] - wp[i]) / n[i] <= hi} | {lo, hi})
    w_at = lambda t: [wp[i] + t * n[i] for i in range(3)]  # noqa: E731
    S = sigma_x(I); mu = m2.mean_vector(I)
    cands = []
    phi = lambda t: sum(w_at(t)[i] - I.w0[i] for i in range(3)) + m2.tau(I, [w_at(t)[i] - I.w0[i] for i in range(3)])  # noqa: E731
    for p, q in zip(bps, bps[1:] + [bps[-1]]):
        cands += [p, q]
        if p < q:
            sl = (phi(q) - phi(p)) / (q - p)          # funding is linear on the piece; add its boundary root
            if sl != 0:
                tr = p + (I.k0 - phi(p)) / sl
                if p <= tr <= q:
                    cands.append(tr)
            mid = (p + q) / 2
            sg = [1 if w_at(mid)[i] > I.w0[i] else -1 for i in range(3)]
            rate = [I.kbuy[i] if sg[i] > 0 else I.ksell[i] for i in range(3)]
            # d/dt Q(w_p + t n) = 0 on this piece
            lin = sum((mu[i] - rate[i] * sg[i]) * n[i] for i in range(3)) - I.gamma * sum(
                wp[i] * S[i][j] * n[j] for i in range(3) for j in range(3))
            quad = I.gamma * sum(n[i] * S[i][j] * n[j] for i in range(3) for j in range(3))
            if quad > 0:
                t = lin / quad
                if p <= t <= q:
                    cands.append(t)
    vals = [Qx(I, w_at(t)) for t in cands if feas(w_at(t))]
    return max(vals) if vals else None


def v_concavity(I):
    """Midpoint concavity of V = fibre max - G on the grid, along rows, columns and both diagonals (exact)."""
    pts = {}
    for i, j in itertools.product(range(GRID + 1), repeat=2):
        b = (Fr(i, GRID), Fr(3 * j, 10 * GRID))
        fm = fibre_max(I, b)
        if fm is not None:
            pts[(i, j)] = fm - G(I, b)
    viol, worst, checked = 0, Fr(0), 0
    for (i, j), v in pts.items():
        for di, dj in ((1, 0), (0, 1), (1, 1), (1, -1)):
            a, c = (i - di, j - dj), (i + di, j + dj)
            if a in pts and c in pts:
                checked += 1
                gap = v - (pts[a] + pts[c]) / 2
                if gap < 0:
                    viol += 1
                    worst = min(worst, gap)
    return dict(points=len(pts), triples=checked, violations=viol, worst=str(worst))


def task(key):
    geom, cost, alpha, gamma, level = key
    I = xinstance(geom, cost, Fr(alpha), Fr(gamma), level)
    ok = psd_ok(I)
    VF, wJ, _ = m2.solve(I, "F", exact=True)
    bstar, s1 = e018.stage1(I, True)
    lam2 = tuple(I.gamma * e018.SF[k] ** 2 * bstar[k] for k in range(2))
    J = XInstance(**{f: getattr(I, f) for f in I.__dataclass_fields__ if f not in ("lam",)}, lam=lam2)
    _, w2, opts = m2.solve(J, "F", exact=True)
    gap = VF - Qx(I, w2)
    nu = [e018.LAM[k] - I.gamma * e018.SF[k] ** 2 * bstar[k] for k in range(2)]
    eJ, e2 = e018.expo(I, wJ), e018.expo(I, w2)
    lin = sum(nu[k] * (eJ[k] - e2[k]) for k in range(2))
    return dict(geom=geom, cost=cost, alpha=alpha, gamma=gamma, level=level, psd=ok, VF=str(VF), gap=str(gap),
                lin=str(lin), bound_holds=gap <= lin, candidates=len(opts), wJ=[str(x) for x in wJ], w2=[str(x) for x in w2],
                bind_J=e018.bind(I, wJ), bind_2S=e018.bind(I, w2), dist=str(sum((eJ[k] - e2[k]) ** 2 for k in range(2))),
                V=v_concavity(I))


def keys():
    return [(g, c, str(a), str(ga), lv) for g, c, a, ga, lv in itertools.product(GEOMS, COSTS, ALPHAS, GAMMAS, LEVELS)]


def run():
    t0 = time.time()
    with Pool(int(os.environ.get("PROCS", "8"))) as pool:
        rows = pool.map(task, keys(), chunksize=1)
    (HERE / "results.json").write_text(json.dumps(rows, indent=0))
    print(f"{len(rows)} cells, seconds: {time.time() - t0:.0f}")


# ---------------------------------------------------------------- Part R: safe-condition rule (018 outputs only)

def features(r):
    return dict(alpha=Fr(r["alpha"]), cost=r["cost"], gamma=Fr(r["gamma"]), geom=r["geom"], start=r.get("start", START))


def conditions(rows):
    cs = []
    for a in sorted({Fr(r["alpha"]) for r in rows}):
        cs += [(f"alpha >= {float(a) * 1e4:.0f} bp", lambda f, a=a: f["alpha"] >= a),
               (f"alpha <= {float(a) * 1e4:.0f} bp", lambda f, a=a: f["alpha"] <= a)]
    for c in sorted({r["cost"] for r in rows}):
        cs.append((f"rates {c}", lambda f, c=c: f["cost"] == c))
    for g in sorted({Fr(r["gamma"]) for r in rows}):
        cs += [(f"gamma >= {g}", lambda f, g=g: f["gamma"] >= g), (f"gamma <= {g}", lambda f, g=g: f["gamma"] <= g)]
    for g in sorted({r["geom"] for r in rows}):
        cs.append((f"geometry {g}", lambda f, g=g: f["geom"] == g))
    for s in sorted({r.get("start", START) for r in rows}):
        cs.append((f"start {s}", lambda f, s=s: f["start"] == s))
    return cs


def fit_rule(rows, gapkey):
    """Registered rule family: a single condition, or the AND / OR of two, predicting 'gap < 1 bp'. Best accuracy,
    ties to fewer false-safe calls, then fewer conditions."""
    y = [Fr(r[gapkey] if isinstance(r[gapkey], str) else r[gapkey]["gap"]) < Fr(1, 10000) for r in rows]
    F = [features(r) for r in rows]
    cs = conditions(rows)
    best = None
    rules = [(n, f, 1) for n, f in cs]
    for (n1, f1), (n2, f2) in itertools.combinations(cs, 2):
        rules.append((f"{n1} AND {n2}", lambda x, f1=f1, f2=f2: f1(x) and f2(x), 2))
        rules.append((f"{n1} OR {n2}", lambda x, f1=f1, f2=f2: f1(x) or f2(x), 2))
    for name, f, k in rules:
        p = [f(x) for x in F]
        acc = sum(pi == yi for pi, yi in zip(p, y))
        fs = sum(pi and not yi for pi, yi in zip(p, y))
        key = (acc, -fs, -k)
        if best is None or key > best[0]:
            best = (key, name, f, acc, fs, sum(p))
    return best, y


def report():
    import statistics
    rows = json.load(open(HERE / "results.json"))
    bp = lambda x: float(Fr(x)) * 1e4  # noqa: E731
    print(f"cells {len(rows)}; joint covariance PSD in {sum(r['psd'] for r in rows)}; stage-2 ties "
          f"{sum(r['candidates'] > 1 for r in rows)}")
    print("\n## Part X: gap, bound and V concavity by cross-moment level\n")
    print("| level | cells | gap 0 | gap < 1 bp | gap >= 1 bp | median gap | max gap | gap <= nu'Delta e | cells with V concave on grid | worst midpoint violation |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for lv in LEVELS:
        rs = [r for r in rows if r["level"] == lv]
        g = [bp(r["gap"]) for r in rs]
        cc = sum(r["V"]["violations"] == 0 for r in rs)
        worst = min(Fr(r["V"]["worst"]) for r in rs)
        print(f"| {lv} | {len(rs)} | {sum(Fr(r['gap']) == 0 for r in rs)} | {sum(x < 1 for x in g)} | {sum(x >= 1 for x in g)} | "
              f"{statistics.median(g):.3f} | {max(g):.3f} | {sum(r['bound_holds'] for r in rs)} | {cc} | {float(worst) * 1e4:.4f} bp |")
    print("\n**change against L0, cell by cell** (same geometry, rates, alpha, gamma):")
    base = {(r["geom"], r["cost"], r["alpha"], r["gamma"]): r for r in rows if r["level"].startswith("L0")}
    for lv in list(LEVELS)[1:]:
        dd = [bp(r["gap"]) - bp(base[(r["geom"], r["cost"], r["alpha"], r["gamma"])]["gap"]) for r in rows if r["level"] == lv]
        print(f"- {lv}: gap change median {statistics.median(dd):+.3f} bp, min {min(dd):+.3f}, max {max(dd):+.3f}; "
              f"up by >= 1 bp in {sum(x >= 1 for x in dd)}, down by >= 1 bp in {sum(x <= -1 for x in dd)}")
    print("\n**V concavity by geometry and level** (cells with no midpoint violation / cells):")
    for g in GEOMS:
        print(f"- {g}: " + "; ".join(f"{lv.split()[0]} {sum(1 for r in rows if r['geom'] == g and r['level'] == lv and r['V']['violations'] == 0)}"
                                      f"/{sum(1 for r in rows if r['geom'] == g and r['level'] == lv)}" for lv in LEVELS))
    print(f"grid points with a nonempty fibre per cell: {min(r['V']['points'] for r in rows)}-{max(r['V']['points'] for r in rows)}; "
          f"triples checked per cell: {min(r['V']['triples'] for r in rows)}-{max(r['V']['triples'] for r in rows)}")
    print("\n**binding constraints where the gap is >= 1 bp**: joint funding tight "
          f"{sum(r['bind_J']['funding'] for r in rows if bp(r['gap']) >= 1)}, joint on a long-only or cap bound "
          f"{sum(bool(r['bind_J']['long_only']) or bool(r['bind_J']['caps']) for r in rows if bp(r['gap']) >= 1)}, of "
          f"{sum(bp(r['gap']) >= 1 for r in rows)}")

    print("\n## Part R: observable safe-condition rule (fit on 018's 720 exact cells, 2S-alpha)\n")
    r18 = json.load(open(ROOT / "experiments" / "018" / "results.json"))
    (key, name, f, acc, fs, npos), y = fit_rule(r18, "2S-alpha")
    print(f"best rule for 'gap < 1 bp': **{name}**; accuracy {acc}/{len(r18)}; predicted safe {npos}, of which false-safe "
          f"(gap >= 1 bp) {fs}; true safe cells {sum(y)}")
    one = max(((sum((c(features(r)) == yy) for r, yy in zip(r18, y)), n) for n, c in conditions(r18)))
    print(f"best single condition: {one[1]} ({one[0]}/{len(r18)})")
    print(f"stage-1 margin (b_u inside the funded exposure set) is never available on 018's grid: b_u is outside in "
          f"{sum(r['stage1_binding'] for r in r18)} of {len(r18)}, so no margin rule can be evaluated")
    # out of sample: the same rule on 020's cross-moment cells (start S1, sA 2%)
    y20 = [bp(r["gap"]) < 1 for r in rows]
    p20 = [f(features(r)) for r in rows]
    print(f"same rule on 020's {len(rows)} cross-moment cells: accuracy {sum(a == b for a, b in zip(p20, y20))}, false-safe "
          f"{sum(a and not b for a, b in zip(p20, y20))}")
    for lv in LEVELS:
        idx = [i for i, r in enumerate(rows) if r["level"] == lv]
        print(f"- {lv}: accuracy {sum(p20[i] == y20[i] for i in idx)}/{len(idx)}, false-safe {sum(p20[i] and not y20[i] for i in idx)}")


if __name__ == "__main__":
    report() if sys.argv[1:] == ["report"] else run()
