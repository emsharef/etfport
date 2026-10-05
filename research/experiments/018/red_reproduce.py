"""Red's reproduction of experiment 018, written from the registered Design without reading run.py.

Cells are experiment 006's Part K grid with the Design's four rate schedules, built by red's experiment
006 builder. Stage 1 is red's exact rational maximization of lambda'b - (gamma/2) b'Sf b over the hull of
0 and the loading rows. Stage 2 is an M2 problem with the same Sigma and mean vector gamma B Sf b*
(+ alpha e_A - c^E for 2S-alpha): red builds it as an M2 instance with lambda replaced by gamma Sf b*
(and alpha, drag zeroed for 2S-lit), solves it with the experiment 004 exact solver (reproduced by red),
and certifies every optimum, joint and stage 2, with red's own exact KKT certificate (experiment 006).
Gaps are evaluated with red's own exact score.

Usage: uv run python experiments/018/red_reproduce.py
"""
import sys
from dataclasses import replace
from fractions import Fraction as Fr
from multiprocessing import Pool
from pathlib import Path
from statistics import median

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "006"))
import red_reproduce as R6  # noqa: E402  (red's experiment 006 builder and certificate)
from m2 import solve  # noqa: E402

BP = Fr(1, 10000)
RATES = {"Z": ((0, 0), (0, 0)), "EQ5": ((5, 5), (5, 5)), "FL-554": ((554, 0), (1, 1)), "DC-100": ((0, 100), (1, 1))}
SF2 = [R6.SF[0] ** 2, R6.SF[1] ** 2]


def G(b, lam, g):
    return lam[0] * b[0] + lam[1] * b[1] - g / 2 * (SF2[0] * b[0] ** 2 + SF2[1] * b[1] ** 2)


def stage1(pts, lam, g):
    """Exact argmax of G over conv(pts): interior optimum if inside, else best point on all segments."""
    bu = (lam[0] / (g * SF2[0]), lam[1] / (g * SF2[1]))
    def inside(b):   # conv of 0 and loading rows: b = sum t_i r_i, t >= 0, sum t <= 1 (2-d: check by LP-free test)
        rows = pts[1:]
        import itertools
        for i, j in itertools.combinations(range(len(rows)), 2):
            r, s = rows[i], rows[j]
            det = r[0] * s[1] - r[1] * s[0]
            if det == 0:
                continue
            t = (b[0] * s[1] - b[1] * s[0]) / det; u = (r[0] * b[1] - r[1] * b[0]) / det
            if t >= 0 and u >= 0 and t + u <= 1:
                return True
        for r in rows:        # segment from 0 to r
            if r[0] * b[1] == r[1] * b[0] and (r[0] * b[0] + r[1] * b[1]) >= 0:
                k = (r[0] * b[0] + r[1] * b[1]) / (r[0] ** 2 + r[1] ** 2)
                if 0 <= k <= 1:
                    return True
        return False
    if inside(bu):
        return bu, False
    best, arg = None, None
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            p, qq = pts[i], pts[j]
            d = (qq[0] - p[0], qq[1] - p[1])
            grad = (lam[0] - g * SF2[0] * p[0], lam[1] - g * SF2[1] * p[1])
            den = g * (SF2[0] * d[0] ** 2 + SF2[1] * d[1] ** 2)
            t = min(max((grad[0] * d[0] + grad[1] * d[1]) / den, Fr(0)), Fr(1)) if den else Fr(0)
            b = (p[0] + t * d[0], p[1] + t * d[1])
            v = G(b, lam, g)
            if best is None or v > best:
                best, arg = v, b
    return arg, True


def one(args):
    geom, rates, al, g, sA, st = args
    I = R6.cell(geom, "Z", al, g, sA, st)
    (ab, as_), (eb, es) = RATES[rates]
    n = len(I.BE)
    I = replace(I, kbuy=(ab * BP,) + (eb * BP,) * n, ksell=(as_ * BP,) + (es * BP,) * n)
    mu, Sig, ok = R6.red_model(I)
    vJ, wJ, _ = solve(I, "F")
    assert R6.certified(I, mu, Sig, wJ, "F")
    B = [I.BA] + list(I.BE)
    bstar, bound = stage1([(Fr(0), Fr(0))] + B, I.lam, g)
    out = dict(geom=geom, rates=rates, alpha=int(al), gamma=int(g), sA=str(sA), start=st, bound=bound, bstar=bstar)
    lam2 = (g * SF2[0] * bstar[0], g * SF2[1] * bstar[1])
    for name, J in (("alpha", replace(I, lam=lam2)), ("lit", replace(I, lam=lam2, alpha=Fr(0), cE=(Fr(0),) * n))):
        mu2, Sig2, _ = R6.red_model(J)
        v2, w2, cands = solve(J, "F")
        assert R6.certified(J, mu2, Sig2, w2, "F")
        out["gap_" + name] = (R6.Q(I, mu, Sig, wJ) - R6.Q(I, mu, Sig, w2)) / BP
        out[name + "_ncand"] = len(cands)
        if name == "alpha":
            bw = [sum(w2[i] * B[i][k] for i in range(len(B))) for k in range(2)]
            out["mismatch"] = g / 2 * sum(SF2[k] * (bw[k] - bstar[k]) ** 2 for k in range(2)) / BP
            out["J_fund_tight"] = R6.slack(I, wJ) == 0
            out["2S_fund_tight"] = R6.slack(I, w2) == 0
            out["J_boundary"] = any(x == 0 or x == 1 for x in wJ)
            bJ = [sum(wJ[i] * B[i][k] for i in range(len(B))) for k in range(2)]
            L = lambda bb: (I.lam[0] - g * SF2[0] * bstar[0]) * (bb[0] - bstar[0]) + (I.lam[1] - g * SF2[1] * bstar[1]) * (bb[1] - bstar[1])
            out["Lterm"] = (L(bJ) - L(bw)) / BP
    # 2S-unc identity: unconstrained target
    bu = (I.lam[0] / (g * SF2[0]), I.lam[1] / (g * SF2[1]))
    Ju = replace(I, lam=(g * SF2[0] * bu[0], g * SF2[1] * bu[1]))
    vu, wu, _ = solve(Ju, "F")
    out["unc"] = (R6.Q(I, mu, Sig, wJ) - R6.Q(I, mu, Sig, wu)) / BP
    return out


def main():
    grid = [(geom, r, al, g, sA, st) for geom in R6.GEOM for r in RATES for al in R6.ALPHA for g in R6.GAMMA
            for sA in R6.SA for st in R6.STARTS]
    with Pool(8) as p:
        res = p.map(one, grid)
    f = float
    print(f"cells {len(res)}; 2S-unc gap exactly 0 in {sum(r['unc'] == 0 for r in res)}; stage 1 binds in {sum(r['bound'] for r in res)}")
    print("b* by gamma:", sorted({(r['gamma'], tuple(round(f(x), 3) for x in r['bstar'])) for r in res}))
    print(f"stage-2 optimum unique in {sum(r['alpha_ncand'] == 1 for r in res)} cells")
    def row(lab, rs, key="gap_alpha"):
        gs = [r[key] for r in rs]
        print(f"  {lab:12s} {len(rs):4d} zero {sum(x == 0 for x in gs):4d} <1 {sum(x < 1 for x in gs):4d} >=1 {sum(x >= 1 for x in gs):4d}"
              f" median {f(median(gs)):.2f} max {f(max(gs)):.2f}")
    print("2S-alpha:")
    row("all", res)
    for rt in RATES:
        row(rt, [r for r in res if r["rates"] == rt])
    row("alpha>0", [r for r in res if r["alpha"] > 0]); row("alpha=0", [r for r in res if r["alpha"] == 0])
    for a in (-25, -50):
        row(f"alpha={a}", [r for r in res if r["alpha"] == a])
    big = [r for r in res if r["gap_alpha"] >= 1]
    print(f"  cells >= 1 bp: {len(big)}; alpha <= 0 among them {sum(r['alpha'] <= 0 for r in big)}; "
          f"L_term share of summed gap {f(sum(r['Lterm'] for r in big) / sum(r['gap_alpha'] for r in big)):.2f}; "
          f"joint funding tight {sum(r['J_fund_tight'] for r in big)}, two-stage {sum(r['2S_fund_tight'] for r in big)}, "
          f"joint on a bound {sum(r['J_boundary'] for r in big)}")
    print(f"  zero-gap cells: {sum(r['gap_alpha'] == 0 for r in res)}, of which alpha > 0: {sum(1 for r in res if r['alpha'] > 0 and r['gap_alpha'] == 0)}"
          f"; big cells at zero rates: {sorted({(r['alpha'], r['geom'], r['gamma']) for r in big if r['rates'] == 'Z'})}")
    zmax = max((r for r in res if r["rates"] == "Z"), key=lambda r: r["gap_alpha"])
    print(f"  Z max cell {zmax['geom']} alpha {zmax['alpha']} gamma {zmax['gamma']} sA {zmax['sA']} {zmax['start']}: {f(zmax['gap_alpha']):.4f} bp")
    mm = [r["mismatch"] for r in res]
    print(f"  mismatch penalty median {f(median(mm)):.2f} max {f(max(mm)):.2f}; gap median by geometry "
          + ", ".join(f"{gm} {f(median([r['gap_alpha'] for r in res if r['geom'] == gm])):.2f}" for gm in R6.GEOM))
    for sA in ("1/100", "1/50"):
        gs = [r["gap_alpha"] for r in res if r["sA"] == sA]
        print(f"  active residual {sA}: median {f(median(gs)):.3f} max {f(max(gs)):.2f}")
    print("2S-lit:")
    row("all", res, "gap_lit")
    for a in (50, 0):
        row(f"alpha={a}", [r for r in res if r["alpha"] == a], "gap_lit")
    z = [r for r in res if r["gap_lit"] == 0]
    print("  lit zero cells:", sorted({(r['rates'], r['alpha'], r['start'], r['gamma']) for r in z}))
    print(f"exact medians: all {f(median([r['gap_alpha'] for r in res])):.4f}; G1-exact {f(median([r['gap_alpha'] for r in res if r['geom'] == 'G1-exact'])):.4f}; "
          f"2S-lit {f(median([r['gap_lit'] for r in res])):.4f}")
    zb = sorted((r["geom"], r["gamma"], r["sA"], r["start"], round(f(r["gap_alpha"]), 3)) for r in big if r["rates"] == "Z")
    print(f"zero-rate cells >= 1 bp: {len(zb)}: {zb}")


if __name__ == "__main__":
    main()
