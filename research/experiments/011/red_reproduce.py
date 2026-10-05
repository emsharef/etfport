"""Red's reproduction of experiment 011, written from the registered Design without reading run.py.

The gate uses red's own exact engine (experiments/009/red_reproduce.py) with this Design's fixture. Where
the Design's quantities can be computed exactly, they are:
- t_{N,eta} and coverage, by exact convolution of three (2B - N)^2/N terms;
- the fallback shortfall, because v_hat_E depends only on lambda_hat_2, a single binomial;
- the deterministic sanity table of Deviation 1;
- claims 015-016's bounds.

Power and false certification are Monte Carlo over the exact sufficient statistics, with red's own
seeds, independent of the analyst's.

Usage: uv run python experiments/011/red_reproduce.py
"""
import itertools
import math
import sys
from collections import defaultdict
from fractions import Fraction as F
from math import comb
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "009"))
import red_reproduce as R  # noqa: E402

M4 = R.M4
D = lambda x: F(str(x))
LAM = (D("0.00897"), D("0.01840"))
SH, SM, SA, SE_ = D("0.06095"), D("0.08540"), D("0.02"), D("0.002")
GAMMA = F(5)
BOX = ((D("-0.01"), D("0.03")), (F(0), D("0.04")), (D("-0.01"), D("0.01")))
OM_DIAG = (SH * SH, SM * SM, SA * SA)
SIG = [[F(3, 10) ** 2 * SH * SH + SM * SM + SA * SA, SM * SM], [SM * SM, SM * SM + SE_ * SE_]]
for mod in (M4, R):
    mod.AM, mod.PM, mod.KM, mod.GAMMA = F(0), F(1, 2), F(1, 2), GAMMA
M4.BA, M4.BE = (F(3, 10), F(1)), (F(0), F(1))          # red's check stores one ETF loading pair
R.S = SIG
R.BOX = M4.BOX = BOX


def set_costs(k):
    for mod in (M4, R):
        mod.KA = mod.KE = k


def quantile(N, eta):
    """Exact law of T_N = sum of three independent (2B - N)^2 / N; returns (t, coverage)."""
    one = defaultdict(F)
    for b in range(N + 1):
        one[(2 * b - N) ** 2] += F(comb(N, b), 2 ** N)
    tot = {0: F(1)}
    for _ in range(3):
        new = defaultdict(F)
        for a, p in tot.items():
            for c, q in one.items():
                new[a + c] += p * q
        tot = new
    acc = F(0)
    for v in sorted(tot):
        acc += tot[v]
        if acc >= 1 - eta:
            return F(v, N), acc


def gate(th_hat, t, N):
    """(certify, empty, w_hat_F, v_hat_E) for the registered vertex gate."""
    wF, vE = R.argmax_F(th_hat), R.argmax_E(th_hat)
    # C_N nonempty: Omega is diagonal, so clip each coordinate to the box
    mm = sum((th_hat[i] - min(max(th_hat[i], BOX[i][0]), BOX[i][1])) ** 2 / OM_DIAG[i] for i in range(3))
    empty = N * mm > t
    if empty or wF[0] == R.AM:
        return False, empty, wF, vE
    r = [M4.ub_sqrt(t * OM_DIAG[i] / N) for i in range(3)]
    box = [(max(BOX[i][0], th_hat[i] - r[i]), min(BOX[i][1], th_hat[i] + r[i])) for i in range(3)]
    ell = min(R.Qy(wF, v) - R.supE(v) for v in itertools.product(*box))
    return ell > 0, empty, wF, vE


def ell_at_truth(al, N, t):
    th = LAM + (al,)
    wF = R.argmax_F(th)
    r = [M4.ub_sqrt(t * OM_DIAG[i] / N) for i in range(3)]
    box = [(max(BOX[i][0], th[i] - r[i]), min(BOX[i][1], th[i] + r[i])) for i in range(3)]
    return min(R.Qy(wF, v) - R.supE(v) for v in itertools.product(*box))


def G_star(al):
    th = LAM + (al,)
    return R.Qy(R.argmax_F(th), th) - R.supE(th)


def main():
    fails = []
    rep_alphas = {"zero": [F(-3703, 10 ** 6), F(-2703, 10 ** 6), F(-297, 200000), F(-389, 500000),
                           F(187, 10 ** 6), F(57, 20000)],
                  "equal 5 bp": [F(-3359, 10 ** 6), F(-2359, 10 ** 6), F(-63, 125000), F(209, 10 ** 6),
                                 F(1153, 10 ** 6), F(753, 200000)]}
    rep_G = {"zero": [0, 0, 2.003, 5.004, 10.004, 25.005], "equal 5 bp": [0, 0, 2.001, 5.002, 10.005, 25.005]}
    rep_short = {"zero": {40: 18.028, 80: 11.591, 160: 6.258}, "equal 5 bp": {40: 18.396, 80: 11.713, 160: 6.236}}
    Ns = (40, 80, 160)
    q = {(N, eta): quantile(N, eta) for N in Ns for eta in (F(1, 20), F(1, 4))}
    print("exact calibration: " + "; ".join(f"N={N}, eta={eta}: t={float(t):.4f}, coverage={float(c):.4f}"
                                             for (N, eta), (t, c) in q.items()))
    for cname, k in (("zero", F(0)), ("equal 5 bp", F(5, 10000))):
        set_costs(k)
        # G_* at the reported alphas, and the zero-gap threshold between the two nulls and the 2 bp point
        Gs = [float(G_star(a)) * 1e4 for a in rep_alphas[cname]]
        ok = all(abs(g - r_) < 0.0015 for g, r_ in zip(Gs, rep_G[cname]))
        print(f"[{cname}] G_* at the reported alphas (bp): {[round(g, 3) for g in Gs]} match: {ok}")
        fails += [] if ok else [f"{cname}: G_* mismatch"]
        # exact fallback shortfall: v_hat_E depends only on lambda_hat_2 = lambda_2 + SM (2B - N)/N
        th_s = LAM + (rep_alphas[cname][0],)
        supE_s = R.supE(th_s)
        for N in Ns:
            ex = sum(F(comb(N, b), 2 ** N) * (supE_s - R.Qy(R.argmax_E((F(0), LAM[1] + SM * F(2 * b - N, N), F(0))), th_s))
                     for b in range(N + 1))
            stay = supE_s - R.Qy((F(0), F(1, 2)), th_s)
            print(f"  N={N}: exact E[fallback shortfall] {float(ex) * 1e4:.3f} bp (reported MC {rep_short[cname][N]}); "
                  f"1/(2 gamma N) = {1e4 / (2 * 5 * N):.2f} bp; staying at the incumbent costs {float(stay) * 1e4:.4f} bp")
            if abs(float(ex) * 1e4 - rep_short[cname][N]) > 1.2:          # three reported SEs
                fails.append(f"{cname} N={N}: shortfall outside 3 SE")
        # deterministic sanity table (Deviation 1) at the zero-cost alphas with G_* = 10, 25 bp
        if cname == "zero":
            t160 = q[(160, F(1, 20))][0]
            for al, lab in ((F(187, 10 ** 6), 10), (F(57, 20000), 25)):
                vals = [float(ell_at_truth(al, N, q[(N, F(1, 20))][0] if N <= 160 else t160)) * 1e4
                        for N in (40, 80, 160, 640, 2560, 10240)]
                print(f"  sanity G_*={lab} bp: ell at the truth (bp) for N = 40..10240: {[round(v, 1) for v in vals]}")
        # Monte Carlo: power and false certification with red's own seeds
        rng = np.random.default_rng(3011)
        Rn = 400
        for N in Ns:
            Bs = rng.binomial(N, 0.5, size=(Rn, 3))
            for eta in (F(1, 20), F(1, 4)):
                t = q[(N, eta)][0]
                for al, g in zip(rep_alphas[cname], rep_G[cname]):
                    th_s = LAM + (al,)
                    cert = false = 0
                    for b in Bs:
                        e = [F(int(2 * bi - N), N) * s for bi, s in zip(b, (SH, SM, SA))]
                        th_h = tuple(th_s[i] + e[i] for i in range(3))
                        c, _, wF, _ = gate(th_h, t, N)
                        cert += c
                        false += c and R.Qy(wF, th_s) - R.supE(th_s) <= 0
                    if cert > 1 or false > 0:
                        print(f"  MC N={N} eta={eta} alpha={al}: certify {cert}/{Rn}, false {false}")
                    if false / Rn > float(eta):
                        fails.append("false certification above eta")
        print(f"  MC ({Rn} histories per N, shared across alphas and eta): no cell with more than one certification "
              f"unless printed above")
    # Claims 015-016 bounds at eps = 1/20, as registered, and with this fixture's own contrasts.
    eps = 1 / 20
    Om = np.diag([float(x) for x in OM_DIAG])
    DH = 0.3 * float(SH)
    s016 = max(d @ Om @ d for d in (np.array([1, 0, 1.]), np.array([1, -1, 1.])))
    s_fix = max(d @ Om @ d for d in (np.array([0.3, 1, 1.]), np.array([0.3, 0, 1.])))
    print("\nbounds in quarters at eps = 1/20 (claim 015 nec/suf, claim 016 nec/suf as registered, 016 nec with the fixture's contrasts):")
    for dl in (2, 5, 10, 25):
        de = dl * 1e-4
        n15 = (DH / de) ** 2 * math.log(1 / eps) / (4 * math.pi ** 2)
        s15 = 32 * (DH / de) ** 2 * math.log(2 / eps)
        n16 = s016 / de ** 2 * math.log(1 / eps) / (16 * math.pi ** 2)
        s16 = 192 * s016 / de ** 2 * math.log(6 / eps)
        nfix = s_fix / de ** 2 * math.log(1 / eps) / (16 * math.pi ** 2)
        print(f"  {dl:>2} bp: {n15:,.0f} / {s15:,.0f} / {n16:,.0f} / {s16:,.0f}; fixture contrasts: {nfix:,.0f}")
    print(f"\nFailures: {len(fails)}")
    for f in fails:
        print(" -", f)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
