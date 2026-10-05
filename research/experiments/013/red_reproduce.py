"""Red's reproduction of experiment 013, written from the registered Design without reading run.py.

Rule (a)'s critical values are exact: T_n under the two-point law is a sum of three independent
(2B - n)^2/n terms, convolved in integers. Rule (b) implements howard2021time eq. (14), read from the
registered text, with Hoeffding's proxy B_j^2. Everything else is red's own Monte Carlo, with seeds
independent of the analyst's. The comparison with the reported tables allows for Monte Carlo error.

Usage: uv run python experiments/013/red_reproduce.py
"""
import math
import re
import sys
from collections import defaultdict
from fractions import Fraction as F
from math import comb
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
LAM = np.array([0.00897, 0.01840])
SD = np.array([0.06095, 0.08540, 0.02])
D = [np.array([1.0, 0, 1]), np.array([1.0, -1, 1])]
SIG = np.array([math.sqrt((d * SD) @ (d * SD)) for d in D])
B = np.array([4 * np.abs(d) @ SD for d in D])
R, NMAX = 20000, 160
ETAS = (0.05, 0.25)
GAPS = (0, 5, 10, 25, 50, 100)


def laws(rng):
    k = np.arange(-200, 201) / 50
    lo, hi = 0.5, 2.0
    for _ in range(100):
        s = (lo + hi) / 2
        p = np.exp(-k ** 2 / (2 * s * s)); p /= p.sum()
        lo, hi = (s, hi) if p @ k ** 2 < 1 else (lo, s)
    return {
        "two-point (assumed)": (np.array([-1.0, 1.0]), np.array([0.5, 0.5])),
        "three-point": (np.array([-3.0, 0, 3]), np.array([1 / 18, 8 / 9, 1 / 18])),
        "skewed right": (np.array([-0.5, 2.0]), np.array([0.8, 0.2])),
        "skewed left": (np.array([0.5, -2.0]), np.array([0.8, 0.2])),
        "lattice normal (exp 012 shape)": (k, p),
    }


def t_exact(n, eta):
    """Exact (1 - eta) quantile of T_n = sum of three independent (2B - n)^2/n, B ~ Bin(n, 1/2),
    with integer counts (total weight 8^n)."""
    one = defaultdict(int)
    for b in range(n + 1):
        one[(2 * b - n) ** 2] += comb(n, b)
    tot = {0: 1}
    for _ in range(3):
        new = defaultdict(int)
        for a, pa in tot.items():
            for c, q in one.items():
                new[a + c] += pa * q
        tot = new
    need = F(1) - F(eta).limit_denominator(100)
    acc, total = 0, 8 ** n
    for v in sorted(tot):
        acc += tot[v]
        if acc * need.denominator >= need.numerator * total:
            return v / n


def howard_u(v, rho, alpha, l0=1.0):
    return np.sqrt((v + rho) * np.log(l0 ** 2 * (v + rho) / (alpha ** 2 * rho)))


def main():
    fails = []
    ns = np.arange(4, NMAX + 1)
    T = {eta: np.array([t_exact(int(n), eta) for n in ns]) for eta in ETAS}
    halfb = {eta: np.array([[howard_u(n * B[j] ** 2, 80 * B[j] ** 2, eta / 2) / n for j in range(2)] for n in ns])
             for eta in ETAS}
    i40, i160 = 40 - 4, 160 - 4
    print(f"sigma_j = {SIG.round(5)}, B_j = {B.round(4)}, B_j^2/sigma_j^2 = {(B ** 2 / SIG ** 2).round(1)}")
    print(f"half-widths at 40 y, eta = 1/20: (a) {(np.sqrt(T[0.05][i160] / 160) * SIG * 1e4).round(0)} bp, "
          f"(b) {(halfb[0.05][i160] * 1e4).round(0)} bp")
    rng = np.random.default_rng(1313)
    rep = {}
    for line in open(HERE.parent / "013-d5-law-free-certificates.md"):
        c = [x.strip() for x in line.split("|")]
        if len(c) == 9 and c[3].startswith("("):
            rep[(c[1], c[2], c[3][:4], 0)] = [float(x) if x != "n/a" else None for x in c[4:8]]
        if len(c) == 12 and c[4].startswith("(") and c[3].isdigit():
            rep[(c[1], c[2], c[4][:4], int(c[3]))] = [float(x) if x != "n/a" else None for x in c[5:9]]
    worst, where = 0.0, None
    ncmp = 0
    for name, (vals, probs) in laws(rng).items():
        U = rng.choice(vals, size=(R, NMAX, 3), p=probs)
        S = np.cumsum(U, axis=1)[:, 3:, :]                         # sums for n = 4..160
        Ubar = S / ns[None, :, None]
        E = [(Ubar * (D[j] * SD)[None, None, :]).sum(-1) for j in range(2)]   # e_j = d_j'J Ubar, shape (R, len(ns))
        for gap in GAPS:
            g = gap * 1e-4
            m = [g + LAM[1], g]                                        # m_0 (cash face), m_1 (ETF face, binding)
            for eta in ETAS:
                dec = {
                    "(a) ": np.minimum(m[0] + E[0] - np.sqrt(T[eta] / ns) * SIG[0], m[1] + E[1] - np.sqrt(T[eta] / ns) * SIG[1]) > 0,
                    "(b) ": np.minimum(m[0] + E[0] - halfb[eta][:, 0], m[1] + E[1] - halfb[eta][:, 1]) > 0,
                    "(c) ": np.minimum(m[0] + E[0], m[1] + E[1]) > 0,
                }
                for rule, d in dec.items():
                    single = [d[:, n - 4].mean() for n in (40, 80, 160)]
                    ever = d.any(1).mean()
                    mine = single + [ever]
                    key = (name, f"{eta:.2f}", rule, gap)
                    if key in rep:
                        for a, b_ in zip(mine, rep[key]):
                            if b_ is not None:
                                ncmp += 1
                                # both are independent MC estimates at R each: SE of the difference
                                se = math.sqrt(2 * max(b_ * (1 - b_), 1e-4) / R)
                                z = abs(a - b_) / se
                                if z > worst:
                                    worst, where = z, (key, round(a, 4), b_)
                    if gap in (0, 25) and name in ("two-point (assumed)", "lattice normal (exp 012 shape)", "skewed left"):
                        print(f"  {name:32s} G*={gap:>3} eta={eta} {rule} single 10/20/40 y "
                              f"{' '.join(f'{x:.4f}' for x in single)}; ever {ever:.4f}")
                    if gap == 0 and rule == "(b) " and ever > 0:
                        fails.append(f"law-free rule certified at the null under {name}")
    print(f"\n{ncmp} matched values; largest |red - reported| in SEs of the difference of two independent "
          f"estimates: {worst:.2f} at {where}")
    if worst > 4.0:
        fails.append("disagreement with the reported table beyond Monte Carlo error")
    # Independence-aware Hoeffding proxy (sum of coordinate proxies), for comparison with the registered L1 proxy.
    Bind = np.array([4 * math.sqrt(((d * SD) ** 2).sum()) for d in D])
    hw = [howard_u(160 * Bind[j] ** 2, 80 * Bind[j] ** 2, 0.025) / 160 * 1e4 for j in range(2)]
    print(f"independence-aware proxy 16 sigma_j^2: 40-year half-widths {np.round(hw, 0)} bp (registered L1 proxy: "
          f"{(halfb[0.05][i160] * 1e4).round(0)} bp)")
    print(f"\nFailures: {len(fails)}")
    for f in fails:
        print(" -", f)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
