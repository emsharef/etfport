"""Experiment 040 report (uv run python experiments/040/report.py), from summary.json."""
import json
from collections import Counter
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent


def main():
    S = json.load(open(HERE / "summary.json")); R = S["rows"]
    print(f"{S['statement']}; {len(R)} draws (500 with N = 3, 500 with N = 1); seconds {S['seconds']:.0f}")
    print(f"- joint value cross-check (w-coordinates against experiment 029's instrument coordinates): largest |difference| {max(r['J_inst_diff'] for r in R):.1e}; "
          f"029's CLARABEL-OSQP disagreement {max(r['dis'] for r in R):.1e}")
    print(f"- joint solves switched to the instrument-coordinate solution (Deviation 2): {sum(r['J_switched'] for r in R)}")
    body = [r for r in R if not r["edge"]]
    print(f"- knife edges set aside: {len(R) - len(body)}")
    print(f"- ETFs at zero at the joint optimum: {dict(Counter(len(r['ZJ']) for r in body))}; at stage 1: {dict(Counter(len(r['Z1']) for r in body))}\n")
    print("## Part 1 (fibre-confined exactness with stage 1's slacks)")
    print(f"- zeta* >= 0 and zeta*_j = 0 where w*_j > (Q x_2)_j: {sum(r['slack_ok'] for r in body)}/{len(body)} (smallest zeta* {min(r['zeta_min'] for r in body):.1e})")
    ag = sum(r["exact_pred"] == r["exact_obs"] for r in body)
    print(f"- band test with zeta* at x_2 = (Lambda <= tolerance): {ag}/{len(body)}; exact {sum(r['exact_obs'] for r in body)}, inexact {sum(not r['exact_obs'] for r in body)}")
    for lab, sel in (("an ETF at zero at the joint optimum", lambda r: bool(r["ZJ"])), ("no ETF at zero at the joint optimum", lambda r: not r["ZJ"]),
                     ("an ETF at zero at stage 1", lambda r: bool(r["Z1"]))):
        rs = [r for r in body if sel(r)]
        print(f"  - {lab}: {sum(r['exact_pred'] == r['exact_obs'] for r in rs)}/{len(rs)} agree; exact {sum(r['exact_obs'] for r in rs)}")
    bad = [r for r in body if r["exact_pred"] != r["exact_obs"]]
    for r in bad[:6]:
        print(f"  - disagreement: {r['kind']} {r['idx']}: Lambda {r['Lam']:.2e}, predicted exact {r['exact_pred']}")
    hx = sum(r["exact_pred"] == (r["x_gap"] <= 1e-5) for r in body)
    print(f"- band test = exactness read on holdings (|x_2 - x_J| <= 1e-5; Deviation 3): {hx}/{len(body)}")
    L = [r["Lam"] for r in body if not r["exact_obs"]]
    print(f"- inexact losses: median {np.median(L) * 1e4:.2f} bp, max {max(L) * 1e4:.2f} bp per quarter\n")
    O = [r for r in body if r["kind"] == "one"]
    print("## Part 2 (one fund)")
    print(f"- fibre interval, formula against the solver's LPs: largest |difference| {max(max(abs(r['lo_f'] - r['lo_s']), abs(r['hi_f'] - r['hi_s'])) for r in O):.1e}")
    print(f"- x_1 in the interval: {sum(r['lo_f'] - 1e-5 <= r['x1'] <= r['hi_f'] + 1e-5 for r in O)}/{len(O)}; at the upper end when an ETF with r_j > 0 is at zero at stage 1: "
          f"{sum(abs(r['x1'] - r['hi_f']) <= 1e-5 for r in O if r['upper'])}/{sum(r['upper'] for r in O)}; at the lower end when r_j < 0: "
          f"{sum(abs(r['x1'] - r['lo_f']) <= 1e-5 for r in O if r['lower'])}/{sum(r['lower'] for r in O)}")
    print(f"- x_2 against the clipped band solution: largest |difference| {max(abs(r['x2'] - r['x2_f']) for r in O):.1e}")
    tj = sum(r["in_int"] == r["exact_obs"] for r in O)
    print(f"- x_J in the interval = x_2 equals x_J (holdings, 1e-5): {sum(r['in_int'] == (r['x_gap'] <= 1e-5) for r in O)}/{len(O)}")
    print(f"- T = J iff x_J in the interval: {tj}/{len(O)} (x_J inside {sum(r['in_int'] for r in O)})")
    for r in [r for r in O if r["in_int"] != r["exact_obs"]][:5]:
        print(f"  - disagreement: idx {r['idx']}: x_J {r['xJ']:.6f}, interval [{r['lo_f']:.6f}, {r['hi_f']:.6f}], Lambda {r['Lam']:.2e}")
    split = [abs(r["part1"] + r["part2"] - r["Lam"]) for r in O]
    print(f"- loss split: |part1 + part2 - Lambda| largest {max(split):.1e}; part 1 >= 0 at {sum(r['part1'] >= -1e-9 for r in O)}/{len(O)}, part 2 >= 0 at {sum(r['part2'] >= -1e-9 for r in O)}/{len(O)}; "
          f"part 2 > 1e-8 at {sum(r['part2'] > 1e-8 for r in O)}")
    print(f"- r_j < 0 draws: {sum(1 for r in O if min(r['r']) < 0)}; fibre floored above 0 there: {sum(1 for r in O if min(r['r']) < 0 and r['lo_f'] > 1e-7)}\n")
    print("## Part 3(a) (soft, unconstrained stage 1)")
    z = [r for r in body if r["ZJ"]]
    print(f"- largest |Lambda_s| {max(abs(r['Lam_s']) for r in body):.1e} overall; {max(abs(r['Lam_s']) for r in z):.1e} where an ETF is at zero at the joint optimum ({len(z)})")
    if "part3b" in S:
        B = S["part3b"]; rc = [r for r in B if r["reach"]]; un = [r for r in B if not r["reach"]]
        g = lambda r: max(r["x_gap"], r["w_gap"])
        E = [r for r in un if r["exact"]]; I = [r for r in un if not r["exact"]]
        print(f"\n## Part 3(b) (soft, stage 1 over W_F; Deviation 5): {len(B)} draws, w_TB reachable at {len(rc)} ({sum(r['kind'] == 'multi' for r in rc)} N = 3, {sum(r['kind'] == 'one' for r in rc)} one fund)")
        print(f"- reachable: exact at {sum(r['exact'] for r in rc)}/{len(rc)}; largest |Lambda_s| {max(abs(r['Lam_s']) for r in rc):.1e}, largest solution gap {max(g(r) for r in rc):.1e}")
        print(f"- nu_E in the normal cone of W_F at w*: {sum(r['cone'] for r in B)}/{len(B)}; nonzero where unreachable: {sum(r['nu_norm'] > 1e-9 for r in un)}/{len(un)}")
        print(f"- 0 <= Lambda_s <= nu_E'(w_J - w_2): {sum(-1e-9 <= r['Lam_s'] <= r['bound'] + 1e-9 for r in un)}/{len(un)} (smallest Lambda_s {min(r['Lam_s'] for r in un):.1e}, smallest slack in the upper bound {min(r['bound'] - r['Lam_s'] for r in un):.1e})")
        print(f"- unreachable: exact (solution gap <= 1e-4) at {len(E)} ({sum(r['kind'] == 'multi' for r in E)} N = 3, {sum(r['kind'] == 'one' for r in E)} one fund), inexact at {len(I)}; "
              f"gaps at most {max(g(r) for r in E):.1e} when exact and at least {min(g(r) for r in I):.1e} when not")
        print(f"- the joint optimum solves the nu_E-tilted stage 2 (to 1e-10 in its objective) iff exact: {sum(r['joint_solves'] == r['exact'] for r in un)}/{len(un)}")
        print(f"- loss test alone (Lambda_s <= 1e-10) against the solution test: {sum(r['exact_loss'] == r['exact'] for r in un)}/{len(un)}; Lambda_s up to {max(r['Lam_s'] for r in E):.1e} when exact, "
              f"from {min(r['Lam_s'] for r in I):.1e} when not")
        print(f"- inexact with the same fund holdings (x gap <= 1e-6), the loss in the ETF exposure alone: {sum(r['x_gap'] <= 1e-6 for r in I)}/{len(I)}")
        print(f"- inexact losses: median {np.median([r['Lam_s'] for r in I]) * 1e4:.2f} bp, max {max(r['Lam_s'] for r in I) * 1e4:.2f} bp per quarter")


if __name__ == "__main__":
    main()
