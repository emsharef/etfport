"""Experiment 006: crossed design in M2 (proposal section 6), registered before any run.
See experiments/006-m2-crossed-design.md. Part K is exact (experiment 004 solver, exact mode); Part M is a
Monte Carlo over estimation histories using the solver's float mode, checked against exact mode (Part V).
Prints Markdown tables.
"""
from __future__ import annotations

import sys
import time
from dataclasses import replace
from fractions import Fraction as Fr
from itertools import product
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "004"))
from m2 import Instance2, check_instance, mean_vector, objective, sigma_formula, solve  # noqa: E402

BP = Fr(1, 10000)
# Calibration (factor side from experiment 001, 1963Q3-2025Q2, per quarter; everything else assumed).
SF = (Fr(427, 5000), Fr(61, 1000))           # Mkt-RF SD 8.54%, HML SD 6.10% (two-point shock sizes)
LAM = (Fr(23, 1250), Fr(897, 100000))        # Mkt-RF mean 1.84%, HML mean 0.897%
BA = (Fr(1), Fr(3, 10))                      # active fund: market 1, HML tilt 0.3 (assumed)
SE_ETF = Fr(1, 500)                          # ETF residual 0.2% per quarter (assumed)
CE = Fr(1, 10000)                            # ETF drag 1 bp per quarter (assumed)

GEOMETRY = {  # ETF menus
    "G1-exact": ((Fr(1), Fr(0)), (Fr(1), Fr(3, 10))),     # E2 carries A's factor exposure exactly
    "G2-missing": ((Fr(1), Fr(0)),),                       # A's HML tilt outside the ETF span
    "G3-infeasible": ((Fr(1), Fr(0)), (Fr(1), Fr(3, 20))), # in the span, but matching A needs short E1
}
COSTS = {  # (kappa+_A, kappa-_A, kappa_ETF both directions); all assumed; SENS hypothetical
    "Z": (Fr(0), Fr(0), Fr(0)),
    "EQ5": (5 * BP, 5 * BP, 5 * BP),
    "ETFC5": (Fr(0), Fr(0), 5 * BP),
    "ETF-stress": (Fr(0), Fr(0), 100 * BP),
    "SENS-load": (Fr(23, 377), Fr(0), BP),                 # 575 bp load as M2 purchase rate (exp 004 B2)
}
ALPHA = [Fr(-1, 200), Fr(-1, 400), Fr(0), Fr(1, 400), Fr(1, 200)]   # -50..+50 bp per quarter
GAMMA = [Fr(2), Fr(5), Fr(10)]
SA = [Fr(1, 100), Fr(1, 50)]                                        # active residual 1% or 2% per quarter
STARTS = {  # same invested share (0.9), hence the same market exposure; E2 not held
    "S1-active-heavy": (Fr(1, 2), Fr(2, 5)),
    "S2-etf-heavy": (Fr(1, 5), Fr(7, 10)),
}
NONTRIVIAL = BP                               # economic non-triviality threshold for the oracle gap

# Part M
M_COSTS = ["Z", "EQ5", "ETFC5"]
M_ALPHA = [Fr(-1, 400), Fr(0), Fr(1, 400)]
M_INFO = ["L", "A", "LA"]                     # estimated: lambda only, alpha only, both
M_T = [40, 160]                               # history length in quarters
M_GAMMA, M_SA, M_START = Fr(5), Fr(1, 50), "S1-active-heavy"
R = 2000
T0_SHRINK = 40                                 # shrinkage: alpha_hat * T / (T + T0)
N_VERIFY = 2                                   # replications per cell also solved exactly (Part V)


def instance(geom, cost, alpha, gamma, sA, start) -> Instance2:
    BE = GEOMETRY[geom]
    n = len(BE)
    ka_b, ka_s, ke = COSTS[cost]
    a0, p10 = STARTS[start]
    w0 = (a0, p10) + (Fr(0),) * (n - 1)
    return Instance2(BA=BA, BE=BE, sf=SF, sA=sA, sE=(SE_ETF,) * n, lam=LAM, alpha=alpha, cE=(CE,) * n,
                     gamma=gamma, kbuy=(ka_b,) + (ke,) * n, ksell=(ka_s,) + (ke,) * n, w0=w0,
                     k0=1 - a0 - p10, wbar=(Fr(1),) * (1 + n))


def part_k():
    rows = []
    for geom, cost, alpha, gamma, sA, start in product(GEOMETRY, COSTS, ALPHA, GAMMA, SA, STARTS):
        I = instance(geom, cost, alpha, gamma, sA, start)
        errs = check_instance(I)
        if errs:
            raise RuntimeError(f"inadmissible K cell {geom} {cost}: {errs}")
        VF, wF, _ = solve(I, "F")
        VE, _, _ = solve(I, "E")
        rows.append((geom, cost, alpha, gamma, sA, start, VF - VE, wF[0] - I.w0[0]))
    return rows


def bp(x) -> str:
    return f"{float(x) * 1e4:.3f}"


def report_k(rows):
    print("### Part K: exact oracle gap G* = V_F - V_E (bp per quarter), full crossed grid\n")
    print("| Geometry | Costs | Cells | Cells with G* > 0 | Cells with G* >= 1 bp | Median G* | Max G* | "
          "Cells where F trades the active fund |")
    print("|---|---|---|---|---|---|---|---|")
    for geom, cost in product(GEOMETRY, COSTS):
        g = [r for r in rows if r[0] == geom and r[1] == cost]
        gaps = sorted(r[6] for r in g)
        print(f"| {geom} | {cost} | {len(g)} | {sum(x > 0 for x in gaps)} | {sum(x >= NONTRIVIAL for x in gaps)} | "
              f"{bp(gaps[len(gaps) // 2])} | {bp(gaps[-1])} | {sum(r[7] != 0 for r in g)} |")
    print("\n#### G* by true alpha (bp per quarter; median over gamma, residual and start), primary costs only\n")
    print("| Geometry | alpha (bp/q) | Z | EQ5 | ETFC5 | ETF-stress |\n|---|---|---|---|---|---|")
    for geom, alpha in product(GEOMETRY, ALPHA):
        cells = []
        for cost in ["Z", "EQ5", "ETFC5", "ETF-stress"]:
            gaps = sorted(r[6] for r in rows if r[0] == geom and r[1] == cost and r[2] == alpha)
            cells.append(bp(gaps[len(gaps) // 2]))
        print(f"| {geom} | {float(alpha) * 1e4:.0f} | " + " | ".join(cells) + " |")


def estimates(I: Instance2, info: str, T: int, rng):
    """M2 scenario law history: each shock is +-size with probability 1/2, independently over T quarters."""
    b = rng.binomial(T, 0.5, size=3)
    lam_hat = tuple(float(I.lam[k]) + float(I.sf[k]) * (2 * b[k] - T) / T for k in range(2))
    alpha_hat = float(I.alpha) + float(I.sA) * (2 * b[2] - T) / T
    lam = lam_hat if "L" in info else tuple(float(x) for x in I.lam)
    alpha = alpha_hat if "A" in info else float(I.alpha)
    return lam, alpha


def part_m():
    out, verify_max = [], 0.0
    for geom, cost, alpha, info, T in product(GEOMETRY, M_COSTS, M_ALPHA, M_INFO, M_T):
        I = instance(geom, cost, alpha, M_GAMMA, M_SA, M_START)
        S = [[float(x) for x in r] for r in sigma_formula(I)]
        mu = [float(x) for x in mean_vector(I)]
        VF = float(solve(I, "F")[0])
        VE = float(solve(I, "E")[0])
        Q = lambda w: float(objective(I, S, mu, w))  # noqa: E731  true conditional score
        reg = {p: [] for p in ("P0", "P1", "P2", "P3")}
        D, trade2, trade3, tau2 = [], 0, 0, []
        for r in range(R):
            rng = np.random.default_rng([2006, T, r])          # common random numbers across cells
            lam, al = estimates(I, info, T, rng)
            Ih = replace(I, lam=lam, alpha=al)
            Is = replace(I, lam=lam, alpha=al * T / (T + T0_SHRINK) if "A" in info else al)
            w1 = solve(Ih, "E", exact=False)[1]
            w2 = solve(Ih, "F", exact=False)[1]
            w3 = solve(Is, "F", exact=False)[1]
            if r < N_VERIFY:
                for J, cls, wf in ((Ih, "E", w1), (Ih, "F", w2), (Is, "F", w3)):
                    Jx = replace(J, lam=tuple(Fr(x) for x in J.lam), alpha=Fr(J.alpha))
                    Vx, _, _ = solve(Jx, cls)
                    Vf = float(objective(J, [[float(x) for x in rr] for rr in sigma_formula(J)],
                                         [float(x) for x in mean_vector(J)], wf))
                    verify_max = max(verify_max, abs(float(Vx) - Vf))
            q0, q1, q2, q3 = Q(list(I.w0)), Q(w1), Q(w2), Q(w3)
            for p, q in (("P0", q0), ("P1", q1), ("P2", q2), ("P3", q3)):
                reg[p].append(VF - q)
            D.append(q2 - q1)
            trade2 += abs(w2[0] - float(I.w0[0])) > 1e-9
            trade3 += abs(w3[0] - float(I.w0[0])) > 1e-9
            tau2.append(sum(float(I.kbuy[i]) * max(w2[i] - float(I.w0[i]), 0) +
                            float(I.ksell[i]) * max(float(I.w0[i]) - w2[i], 0) for i in range(I.d)))
        m = lambda x: (float(np.mean(x)), float(np.std(x, ddof=1) / np.sqrt(len(x))))  # noqa: E731
        out.append(dict(geom=geom, cost=cost, alpha=alpha, info=info, T=T, G=VF - VE,
                        reg={p: m(v) for p, v in reg.items()}, D=m(D), Dneg=float(np.mean(np.array(D) < 0)),
                        tr2=trade2 / R, tr3=trade3 / R, tau2=m(tau2)))
    return out, verify_max


def report_m(out, verify_max):
    print(f"\n### Part M: estimation (gamma = {M_GAMMA}, active residual {float(M_SA):.0%}, start {M_START}, "
          f"R = {R}, common random numbers)\n")
    print("Values in bp per quarter, MC mean (SE). Regret = V_F(theta) - Q(w_P; theta). "
          "P0 no trade; P1 ETF-only with estimated means; P2 full trading with estimated means; "
          "P3 full trading with alpha shrunk by T/(T+40). D = Q(P2) - Q(P1), paired.\n")
    print("| Geometry | Costs | alpha | Estimated | T | G* | Regret P0 | Regret P1 | Regret P2 | Regret P3 | "
          "D mean (SE) | P(D<0) | P2 trades active | P3 trades active | P2 cost |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    f = lambda t: f"{t[0] * 1e4:.3f} ({t[1] * 1e4:.3f})"  # noqa: E731
    for o in out:
        print(f"| {o['geom']} | {o['cost']} | {float(o['alpha']) * 1e4:.0f} | {o['info']} | {o['T']} | "
              f"{float(o['G']) * 1e4:.3f} | {f(o['reg']['P0'])} | {f(o['reg']['P1'])} | {f(o['reg']['P2'])} | "
              f"{f(o['reg']['P3'])} | {f(o['D'])} | {o['Dneg']:.3f} | {o['tr2']:.3f} | {o['tr3']:.3f} | "
              f"{f(o['tau2'])} |")
    over = [o for o in out if o["D"][1] * 1e4 > 0.1]
    print(f"\nCells missing the precision target SE(D) <= 0.1 bp: {len(over)} of {len(out)}.")
    print(f"Part V: max |exact - float| value over {N_VERIFY} replications per cell and 3 solves each: "
          f"{verify_max:.3e}")
    flip = [o for o in out if o["G"] > 0 and o["D"][0] + 2 * o["D"][1] < 0]
    print(f"Cells with G* > 0 where D's mean + 2 SE < 0 (estimation reverses the oracle ranking): {len(flip)}")


def main() -> None:
    t0 = time.time()
    report_k(part_k())
    out, vmax = part_m()
    report_m(out, vmax)
    print(f"\nseconds: {time.time() - t0:.0f}")


if __name__ == "__main__":
    main()
