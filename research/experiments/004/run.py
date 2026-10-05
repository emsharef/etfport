"""Experiment 004: verify the exact M2 reference solver (separate purchase and sale rates, signed c^E).
See experiments/004-m2-reference-solver.md. Prints every table in Markdown; exits non-zero on any failure.
"""
from __future__ import annotations

import importlib.util
import sys
import time
from dataclasses import replace
from fractions import Fraction as Fr
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "002"))
import m1  # noqa: E402
from m2 import Instance2, check_instance, feasible, mean_vector, objective, sigma_formula, solve, tau  # noqa: E402

SEED = 2004
N_PER_MENU = 200          # random M2 instances per menu size (n = 1, 2), parts V0-V3
N_EMBED_PER_MENU = 100    # random M1 instances per menu size for the embedding check V4
N_POINTS = 200
TOL_CVX = 1e-6
KGRID = [Fr(0), Fr(1, 10000), Fr(5, 10000), Fr(25, 10000), Fr(1, 100), Fr(61, 1000)]
CEGRID = [Fr(-5, 10000), Fr(-1, 10000), Fr(0), Fr(1, 10000), Fr(5, 10000)]


def exp002_run():
    spec = importlib.util.spec_from_file_location("exp002_run", HERE.parent / "002" / "run.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


R2 = exp002_run()


def to_m2(I: m1.Instance) -> Instance2:
    return Instance2(I.BA, I.BE, I.sf, I.sA, I.sE, I.lam, I.alpha, I.cE, I.gamma, I.kappa, I.kappa,
                     I.w0, I.k0, I.wbar)


def random_m2(rng, n: int) -> Instance2:
    while True:
        base = to_m2(R2.random_instance(rng, n))
        d = base.d
        I = replace(base,
                    kbuy=tuple(KGRID[int(rng.integers(len(KGRID)))] for _ in range(d)),
                    ksell=tuple(KGRID[int(rng.integers(len(KGRID)))] for _ in range(d)),
                    cE=tuple(CEGRID[int(rng.integers(len(CEGRID)))] for _ in range(n)))
        if not check_instance(I):
            return I


def cvx_value(I: Instance2, cls: str) -> float:
    import cvxpy as cp
    d = I.d
    S = np.array([[float(x) for x in r] for r in sigma_formula(I)])
    mu = np.array([float(x) for x in mean_vector(I)])
    kb = np.array([float(x) for x in I.kbuy])
    ks = np.array([float(x) for x in I.ksell])
    w0 = np.array([float(x) for x in I.w0])
    w = cp.Variable(d)
    v = w - w0
    cost = kb @ cp.pos(v) + ks @ cp.neg(v)
    obj = mu @ w - float(I.gamma) / 2 * cp.quad_form(w, cp.psd_wrap(S)) - cost
    cons = [w >= 0, w <= np.array([float(x) for x in I.wbar]), cp.sum(v) + cost <= float(I.k0)]
    if cls == "E":
        cons.append(w[0] == w0[0])
    prob = cp.Problem(cp.Maximize(obj), cons)
    prob.solve(solver="CLARABEL")
    return float(prob.value)


def random_points(rng, I: Instance2, cls: str, k: int):
    d, pts, tries = I.d, [], 0
    while len(pts) < k and tries < 50 * k:
        tries += 1
        w = [Fr(int(rng.integers(0, 1001)), 1000) * I.wbar[i] for i in range(d)]
        if cls == "E":
            w[0] = I.w0[0]
        if rng.random() < 0.3:
            i = int(rng.integers(d))
            if not (cls == "E" and i == 0):
                w = list(I.w0)
                w[i] = min(I.wbar[i], max(Fr(0), I.w0[i] + Fr(int(rng.integers(-50, 51)), 1000)))
        if feasible(I, w):
            pts.append(w)
    return pts


def part_v(rng):
    fails, rows = [], []
    worst, n_pts, n_inst, n_asym, n_negc, n_sing, n_lp = 0.0, 0, 0, 0, 0, 0, 0
    t0 = time.time()
    for n in (1, 2):
        for _ in range(N_PER_MENU):
            I = random_m2(rng, n)
            n_inst += 1
            n_asym += I.kbuy != I.ksell
            n_negc += any(c < 0 for c in I.cE)
            S, mu = sigma_formula(I), mean_vector(I)
            n_sing += not m1.positive_definite(S)
            n_lp += I.gamma == 0
            for cls in ("F", "E"):
                V, w, _ = solve(I, cls)
                if not feasible(I, w) or objective(I, S, mu, w) != V:
                    fails.append(f"V0: returned point infeasible or value mismatch ({cls})")
                diff = abs(float(V) - cvx_value(I, cls))
                worst = max(worst, diff)
                if diff > TOL_CVX:
                    fails.append(f"V1: |exact - CLARABEL| = {diff:.3g} ({cls}, n={n})")
                for p in random_points(rng, I, cls, N_POINTS):
                    n_pts += 1
                    if objective(I, S, mu, p) > V:
                        fails.append(f"V2: feasible point beats the solver ({cls}, n={n})")
                if cls == "E" and not (solve(I, "F")[0] >= V >= solve(I, "N")[0]):
                    fails.append("V3: nesting V_F >= V_E >= V_N violated")
    rows += [("M2 instances (n=1 and n=2)", n_inst), ("  with kappa^+ != kappa^-", n_asym),
             ("  with some c^E < 0", n_negc), ("  with singular Sigma", n_sing), ("  with gamma = 0", n_lp),
             ("V1: max |exact - CLARABEL| over F and E", f"{worst:.3e}"),
             ("V2: random feasible points evaluated exactly", n_pts)]
    # V4: embedding. M1 instances (002's generator) as M2 instances with kappa^+ = kappa^- = kappa.
    n_emb = 0
    for n in (1, 2):
        for _ in range(N_EMBED_PER_MENU):
            I1 = R2.random_instance(rng, n)
            if m1.check_instance(I1):
                continue
            n_emb += 1
            for cls in ("F", "E"):
                V1_, w1_, o1 = m1.solve(I1, cls)
                V2_, w2_, o2 = solve(to_m2(I1), cls)
                if V1_ != V2_ or sorted(map(tuple, o1)) != sorted(map(tuple, o2)):
                    fails.append(f"V4: M2 solver differs from M1 solver on an M1 instance ({cls}, n={n})")
    rows += [("V4: M1 instances solved by both solvers (F and E), exact comparison", n_emb),
             ("seconds", f"{time.time() - t0:.0f}")]
    return rows, fails


def part_b():
    rows, fails = [], []

    def show(x):
        return "(" + ", ".join(str(y) for y in x) + ")" if isinstance(x, tuple) else str(x)

    def report(name, got, expected):
        ok = got == expected
        rows.append((name, show(got), show(expected), "match" if ok else "MISMATCH"))
        if not ok:
            fails.append(f"B: {name}: got {got}, expected {expected}")

    # B1: one-sided purchase rate, signed drag, hand-derived closed form (derivation in the experiment file).
    k, g, alpha, cE = Fr(1, 400), Fr(2), Fr(3, 1000), Fr(-1, 10000)
    I = Instance2(BA=(Fr(1), Fr(0)), BE=((Fr(1), Fr(0)),), sf=(Fr(2, 25), Fr(1, 25)), sA=Fr(1, 50), sE=(Fr(0),),
                  lam=(Fr(3, 200), Fr(0)), alpha=alpha, cE=(cE,), gamma=g, kbuy=(k, Fr(0)), ksell=(Fr(0), Fr(0)),
                  w0=(Fr(0), Fr(1)), k0=Fr(0), wbar=(Fr(1), Fr(1)))
    errs = check_instance(I)
    if errs:
        fails.append(f"B1 instance inadmissible: {errs}")
    muA, muE = mean_vector(I)
    s2, sig2 = I.sf[0] ** 2, I.sA ** 2
    a = (muA - (1 + k) * muE - k + g * k * s2) / (g * (sig2 + k * k * s2))
    p = 1 - (1 + k) * a
    nu = muE - g * s2 * (a + p)
    pre = 0 < a < 1 and 0 < p < 1 and nu >= 0
    rows.append(("B1 precondition: 0 < a*, p* < 1 and budget multiplier >= 0", str(pre), "True",
                 "match" if pre else "MISMATCH"))
    if not pre:
        fails.append("B1: closed-form preconditions fail; benchmark instance mis-chosen")
    V, w, opt = solve(I, "F")
    report("B1 full optimum (a, p) = closed form", tuple(w), (a, p))
    report("B1 optimum unique", len(opt), 1)

    # B2: load conversion. A load L on the offering price is kappa^+ = L/(1-L) on value delivered.
    L = Fr(575, 10000)
    kp = L / (1 - L)
    report("B2 kappa^+ for L = 575 bp (exact)", kp, Fr(23, 377))
    report("B2 kappa^+ in bp, rounded", round(float(kp) * 1e4), 610)
    J = replace(I, kbuy=(kp, Fr(0)))
    x = Fr(1, 10)
    report("B2 cash outlay for x = 1/10 delivered: x + tau = x / (1 - L)", x + tau(J, [x, Fr(0)]), x / (1 - L))
    return rows, fails


def main() -> int:
    rng = np.random.default_rng(SEED)
    brows, bfails = part_b()
    print("### Part B: benchmarks (exact rationals)\n")
    print("| Quantity | Solver or formula | Expected | |\n|---|---|---|---|")
    for r in brows:
        print("| " + " | ".join(r) + " |")
    vrows, vfails = part_v(rng)
    print("\n### Part V: verification\n")
    print("| Item | Value |\n|---|---|")
    for k, v in vrows:
        print(f"| {k} | {v} |")
    fails = bfails + vfails
    print(f"\nFailures: {len(fails)}")
    for f in fails[:50]:
        print("-", f)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
