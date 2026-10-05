"""Red: reproduce experiment 018 Deviation 1 (claim 027's fibre-confined procedure on the 180 zero-rate cells),
with red's exact stage 1 (experiment 018), red's exact fibre maximization (experiment 020) and red's KKT certificate.

Usage: uv run python experiments/018/red_dev1.py
"""
import importlib.util, sys
from fractions import Fraction as Fr
from multiprocessing import Pool
from statistics import median
sys.path.insert(0, "experiments/020")
def load(n, p):
    s = importlib.util.spec_from_file_location(n, p); m = importlib.util.module_from_spec(s); s.loader.exec_module(m); return m
R20 = load("red020", "experiments/020/red_reproduce.py")
R18, R6, m2 = R20.R18, R20.R6, R20.m2
BP = Fr(1, 10000)
def one(args):
    geom, al, g, sA, st = args
    I = R6.cell(geom, "Z", al, g, sA, st)
    mu, Sig, _ = R6.red_model(I)
    _, wJ, _ = m2.solve(I, "F"); assert R6.certified(I, mu, Sig, wJ, "F")
    J = R6.Q(I, mu, Sig, wJ)
    bstar, _ = R18.stage1([(Fr(0), Fr(0))] + [I.BA] + list(I.BE), I.lam, g)
    T = R20.fibre_max(I, mu, Sig, bstar)
    # soft target for comparison
    Js = __import__("dataclasses").replace(I, lam=(g * R18.SF2[0] * bstar[0], g * R18.SF2[1] * bstar[1]))
    _, w2, _ = m2.solve(Js, "F")
    return dict(geom=geom, al=int(al), g=int(g), fib=(J - T) / BP, soft=(J - R6.Q(I, mu, Sig, w2)) / BP)
if __name__ == "__main__":
    grid = [(geom, al, g, sA, st) for geom in R6.GEOM for al in R6.ALPHA for g in R6.GAMMA for sA in R6.SA for st in R6.STARTS]
    with Pool(8) as p:
        res = p.map(one, grid)
    f = float
    for k in ("fib", "soft"):
        v = [r[k] for r in res]
        print(f"{k}: cells {len(v)}, exactly 0 {sum(x == 0 for x in v)}, < 1 {sum(x < 1 for x in v)}, >= 1 {sum(x >= 1 for x in v)}, median {f(median(v)):.3f}, max {f(max(v)):.1f}")
    d = [r["fib"] - r["soft"] for r in res]
    print(f"confined worse {sum(x > 0 for x in d)}, better {sum(x < 0 for x in d)}, equal {sum(x == 0 for x in d)}; difference {f(min(d)):.1f} to {f(max(d)):.1f}")
    for gm in R6.GEOM:
        print(f"  max by geometry {gm}: {f(max(r['fib'] for r in res if r['geom'] == gm)):.1f}")
    for a in (-50, -25):
        print(f"  max at alpha {a}: {f(max(r['fib'] for r in res if r['al'] == a)):.1f}")
    print(f"  max at alpha >= 0: {f(max(r['fib'] for r in res if r['al'] >= 0)):.1f}")
