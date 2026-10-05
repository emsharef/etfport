"""Experiment 002: verify the exact M1 reference solver and reproduce benchmarks.
See experiments/002-m1-reference-solver.md. Prints every table in Markdown; exits non-zero on any failure.
"""
from __future__ import annotations

import sys
import time
from fractions import Fraction as Fr
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from m1 import (Instance, check_instance, feasible, mean_vector, objective, positive_definite,  # noqa: E402
                sigma_formula, solve)

SEED = 2002
N_PER_MENU = 200          # random instances per ETF-menu size (n = 1, 2)
N_POINTS = 200            # random feasible points per instance and class (part V2)
TOL_CVX = 1e-6            # part V1 agreement threshold (absolute, score units)

GRID = {
    "b": [Fr(-1, 2), Fr(-1, 4), Fr(0), Fr(1, 4), Fr(1, 2)],
    "e": [Fr(-1, 2), Fr(-1, 4), Fr(0), Fr(1, 4), Fr(1, 2)],
    "sf1": [Fr(3, 50), Fr(2, 25), Fr(1, 10)],
    "sf2": [Fr(1, 50), Fr(3, 100), Fr(1, 25)],
    "sA": [Fr(1, 100), Fr(1, 50), Fr(3, 100)],
    "sE": [Fr(0), Fr(1, 200)],
    "lam1": [Fr(1, 100), Fr(3, 200), Fr(1, 50)],
    "lam2": [Fr(-1, 200), Fr(0), Fr(1, 200), Fr(1, 100)],
    "alpha": [Fr(-1, 200), Fr(-1, 400), Fr(0), Fr(1, 400), Fr(1, 200)],
    "cE": [Fr(0), Fr(1, 10000), Fr(5, 10000)],
    "gamma": [Fr(0), Fr(1), Fr(2), Fr(5), Fr(10)],
    "kappa": [Fr(0), Fr(1, 10000), Fr(5, 10000), Fr(25, 10000), Fr(1, 100)],
    "wbar": [Fr(1), Fr(1, 2)],
}


def pick(rng, key):
    v = GRID[key]
    return v[int(rng.integers(len(v)))]


def random_instance(rng, n: int) -> Instance:
    d = 1 + n
    BE = [(Fr(1), Fr(0))] + [(Fr(1), pick(rng, "e")) for _ in range(n - 1)]
    while True:
        u = [int(x) for x in rng.integers(0, 11, size=d + 1)]
        if sum(u):
            break
    w0 = tuple(Fr(x, sum(u)) for x in u[:d])
    k0 = Fr(u[d], sum(u))
    wbar = tuple(max(pick(rng, "wbar"), Fr(0)) for _ in range(d))
    wbar = tuple(b if w <= b else Fr(1) for w, b in zip(w0, wbar))
    return Instance(
        BA=(Fr(1), pick(rng, "b")), BE=tuple(BE), sf=(pick(rng, "sf1"), pick(rng, "sf2")),
        sA=pick(rng, "sA"), sE=tuple(pick(rng, "sE") for _ in range(n)),
        lam=(pick(rng, "lam1"), pick(rng, "lam2")), alpha=pick(rng, "alpha"),
        cE=tuple(pick(rng, "cE") for _ in range(n)), gamma=pick(rng, "gamma"),
        kappa=tuple(pick(rng, "kappa") for _ in range(d)), w0=w0, k0=k0, wbar=wbar)


def cvx_value(I: Instance, cls: str) -> float:
    import cvxpy as cp
    d = I.d
    S = np.array([[float(x) for x in r] for r in sigma_formula(I)])
    mu = np.array([float(x) for x in mean_vector(I)])
    kap = np.array([float(x) for x in I.kappa])
    w0 = np.array([float(x) for x in I.w0])
    w = cp.Variable(d)
    v = w - w0
    obj = mu @ w - float(I.gamma) / 2 * cp.quad_form(w, cp.psd_wrap(S)) - kap @ cp.abs(v)
    cons = [w >= 0, w <= np.array([float(x) for x in I.wbar]),
            cp.sum(v) + kap @ cp.abs(v) <= float(I.k0)]
    if cls == "E":
        cons.append(w[0] == w0[0])
    prob = cp.Problem(cp.Maximize(obj), cons)
    prob.solve(solver="CLARABEL")
    return float(prob.value)


def random_feasible_points(rng, I: Instance, cls: str, k: int):
    d, pts, tries = I.d, [], 0
    while len(pts) < k and tries < 50 * k:
        tries += 1
        w = [Fr(int(rng.integers(0, 1001)), 1000) * I.wbar[i] for i in range(d)]
        if cls == "E":
            w[0] = I.w0[0]
        if rng.random() < 0.3:     # also sample near the pre-trade point, where kinks are
            i = int(rng.integers(d))
            if not (cls == "E" and i == 0):
                w = list(I.w0)
                w[i] = min(I.wbar[i], max(Fr(0), I.w0[i] + Fr(int(rng.integers(-50, 51)), 1000)))
        if feasible(I, w):
            pts.append(w)
    return pts


def part_v(rng):
    fails, rows = [], []
    worst_cvx, n_pts, n_inst, n_sing, n_lp = 0.0, 0, 0, 0, 0
    t0 = time.time()
    for n in (1, 2):
        for _ in range(N_PER_MENU):
            I = random_instance(rng, n)
            errs = check_instance(I)
            if errs:
                fails.append(f"inadmissible random instance: {errs}")
                continue
            n_inst += 1
            S = sigma_formula(I)
            n_sing += not positive_definite(S)
            n_lp += I.gamma == 0
            mu = mean_vector(I)
            for cls in ("F", "E"):
                V, w, _ = solve(I, cls)
                if not feasible(I, w) or objective(I, S, mu, w) != V:
                    fails.append(f"V0: returned point infeasible or value mismatch ({cls})")
                vc = cvx_value(I, cls)
                diff = abs(float(V) - vc)
                worst_cvx = max(worst_cvx, diff)
                if diff > TOL_CVX:
                    fails.append(f"V1: |exact - CLARABEL| = {diff:.3g} ({cls}, n={n})")
                for p in random_feasible_points(rng, I, cls, N_POINTS):
                    n_pts += 1
                    if objective(I, S, mu, p) > V:
                        fails.append(f"V2: feasible point beats the solver ({cls}, n={n})")
                if cls == "E":
                    VF = solve(I, "F")[0]
                    VN = solve(I, "N")[0]
                    if not (VF >= V >= VN):
                        fails.append("V3: nesting V_F >= V_E >= V_N violated")
    rows.append(("instances (n=1 and n=2)", n_inst))
    rows.append(("  with singular Sigma", n_sing))
    rows.append(("  with gamma = 0 (linear objective)", n_lp))
    rows.append(("V1: max |exact - CLARABEL| over F and E", f"{worst_cvx:.3e}"))
    rows.append(("V2: random feasible points evaluated exactly", n_pts))
    rows.append(("seconds", f"{time.time() - t0:.0f}"))
    return rows, fails


BENCH = []


def economy(BA, BEs, lam, alpha, cE, gamma, w0, k0, kappa=None):
    n = len(BEs)
    I = Instance(BA=BA, BE=tuple(BEs), sf=(Fr(2, 25), Fr(1, 25)), sA=Fr(1, 50), sE=tuple([Fr(0)] * n),
                 lam=lam, alpha=alpha, cE=tuple([cE] * n), gamma=gamma,
                 kappa=tuple(kappa or [Fr(0)] * (1 + n)), w0=w0, k0=k0, wbar=tuple([Fr(1)] * (1 + n)))
    BENCH.append(I)
    return I


def part_b():
    """Red's funded M1 cases (board/FINDINGS.md 2026-09-27; checks/red-d1-mechanism/check.py) and the
    interior Markowitz closed form. Expected values are red's asserted numbers."""
    rows, fails = [], []

    def show(x):
        return "(" + ", ".join(str(y) for y in x) + ")" if isinstance(x, tuple) else str(x)

    def report(name, got, expected):
        ok = got == expected
        rows.append((name, show(got), show(expected), "match" if ok else "MISMATCH"))
        if not ok:
            fails.append(f"B: {name}: got {got}, expected {expected}")

    h = Fr(1, 2)
    I = economy((Fr(1), h), [(Fr(1), Fr(0))], (Fr(3, 200), Fr(1, 1000)), Fr(0), Fr(0), Fr(5, 4), (h, h), Fr(0))
    VF, wF, _ = solve(I, "F"); VE, wE, _ = solve(I, "E")
    report("1a funded full optimum", tuple(wF), (h, h))
    report("1a funded ETF-only optimum", tuple(wE), (h, h))
    report("1a funded advantage V_F - V_E", VF - VE, Fr(0))

    I0 = economy((Fr(1), h), [(Fr(1), Fr(-2, 5))], (Fr(3, 200), Fr(0)), Fr(0), Fr(0), Fr(5, 4), (Fr(0), Fr(1)), Fr(0))
    VF, wF, _ = solve(I0, "F")
    report("1b funded full optimum (from all-ETF start)", tuple(wF), (Fr(18, 53), Fr(35, 53)))
    I = economy((Fr(1), h), [(Fr(1), Fr(-2, 5))], (Fr(3, 200), Fr(0)), Fr(0), Fr(0), Fr(5, 4),
                (Fr(18, 53), Fr(35, 53)), Fr(0))
    VF, wF, _ = solve(I, "F"); VE, wE, _ = solve(I, "E")
    report("1b funded advantage at that holding", VF - VE, Fr(0))

    I = economy((Fr(1), h), [(Fr(1), Fr(0)), (Fr(1), Fr(2, 5))], (Fr(3, 200), Fr(0)), Fr(3, 5000), Fr(0), Fr(2),
                (h, h, Fr(0)), Fr(0))
    VF, wF, _ = solve(I, "F"); VE, wE, _ = solve(I, "E")
    report("2 funded long-only full optimum", tuple(wF), (Fr(3, 8), Fr(5, 8), Fr(0)))
    report("2 funded ETF-only optimum", tuple(wE), (h, h, Fr(0)))
    report("2 funded advantage V_F - V_E", VF - VE, Fr(1, 80000))

    for label, drag, exp_a in (("once", Fr(1, 10000), Fr(0)), ("twice", Fr(2, 10000), Fr(1, 10))):
        I = economy((Fr(1), Fr(0)), [(Fr(1), Fr(0))], (Fr(3, 200), Fr(0)), Fr(-3, 20000), drag, Fr(5, 4),
                    (Fr(0), Fr(1)), Fr(0))
        VF, wF, _ = solve(I, "F"); VE, _, _ = solve(I, "E")
        report(f"3 drag counted {label}: full-trading active holding", wF[0], exp_a)
        if label == "once":
            report("3 drag counted once: advantage", VF - VE, Fr(0))

    # Interior closed form: kappa = 0, slack budget and limits => w* = (gamma Sigma)^(-1) mu.
    # Deviation 1: (lam, alpha) are backed out so that the closed form is (1/10, 1/10, 1/10): with ETF
    # loadings spanning R^2 and c^E = 0, lam solves the ETF rows of mu = gamma Sigma w*, alpha the active row.
    from m1 import _solve_linear
    BA, BEs, gam, wstar = (Fr(1), h), [(Fr(1), Fr(0)), (Fr(1), Fr(2, 5))], Fr(10), [Fr(1, 10)] * 3
    S0 = sigma_formula(economy(BA, BEs, (Fr(0), Fr(0)), Fr(0), Fr(0), gam, (Fr(0), Fr(0), Fr(0)), Fr(1)))
    BENCH.pop()
    target = [gam * sum(S0[i][j] * wstar[j] for j in range(3)) for i in range(3)]
    lam = tuple(_solve_linear([list(r) for r in BEs], target[1:], True))
    alpha = target[0] - (BA[0] * lam[0] + BA[1] * lam[1])
    I = economy(BA, BEs, lam, alpha, Fr(0), gam, (Fr(1, 10), Fr(1, 10), Fr(1, 10)), Fr(7, 10))
    rows.append(("B0 instance: lam, alpha", f"({lam[0]}, {lam[1]}), {alpha}", "", "assumed"))
    S, mu = sigma_formula(I), mean_vector(I)
    closed = _solve_linear([[I.gamma * x for x in r] for r in S], mu, True)
    interior = all(0 < x < 1 for x in closed) and sum(closed) < 1
    rows.append(("B0 closed form is interior (precondition)", str(interior), "True",
                 "match" if interior else "MISMATCH"))
    if not interior:
        fails.append("B0: closed-form point not interior; benchmark instance mis-chosen")
    VF, wF, opt = solve(I, "F")
    report("B0 full optimum equals (gamma Sigma)^-1 mu", tuple(wF), tuple(closed))
    report("B0 optimum unique (Sigma positive definite, one optimal candidate)",
           positive_definite(S) and len(opt) == 1, True)
    for I_ in BENCH:
        errs = check_instance(I_)
        if errs:
            fails.append(f"B: benchmark instance inadmissible: {errs}")
    return rows, fails


def main() -> int:
    rng = np.random.default_rng(SEED)
    brows, bfails = part_b()
    print("### Part B: benchmark reproduction (exact rationals)\n")
    print("| Quantity | Solver | Expected | |\n|---|---|---|---|")
    for r in brows:
        print("| " + " | ".join(r) + " |")
    vrows, vfails = part_v(rng)
    print("\n### Part V: solver verification on random M1 instances\n")
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
