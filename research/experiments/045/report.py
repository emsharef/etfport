"""Experiment 045 report (uv run python experiments/045/report.py), from summary.json."""
import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent


def main():
    S = json.load(open(HERE / "summary.json")); print(S["statement"], "\n")
    A = S["c110"]
    print(f"## Claim 110: {len(A)} draws (N = 1, 3, 6; sigma_E > 0 at {sum(a['sE'] > 0 for a in A)}); binding budget at {sum(a['binding'] for a in A)}")
    print(f"- holdings (funds and ETF), reduction against the joint solver: largest |difference| {max(a['dx'] for a in A):.1e} (CLARABEL against OSQP {max(a['solver_dx'] for a in A):.1e})")
    print(f"- ETF status: {sum(a['st'] == a['stJ'] for a in A)}/{len(A)} ({dict(Counter(a['st'] for a in A))}); m* against mu_E - gamma sigma_EE w*: {max(abs(a['m'] - a['mJ']) for a in A):.1e}; "
          f"eta* against the budget dual: {max(abs(a['eta'] - a['etaJ']) for a in A):.1e}")
    print(f"- k(x(eta)) nondecreasing on 50 values: {sum(a['k_mono'] for a in A)}/{len(A)}; q(m, eta) nondecreasing in m: {sum(a['q_mono'] for a in A)}/{len(A)}")
    print(f"- part 4(a) direction from the incumbent: {sum(a['dir_ok'] for a in A)}/{len(A)}; the miss: {[(a['idx'], a['dx']) for a in A if not a['dir_ok']]} (Deviation 3)\n")
    R = S["c111"]
    for nm, title in (("aware", "incumbent-aware first stage"), ("041", "claim 041's first stage")):
        X = [r[nm] for r in R if r[nm] is not None]
        print(f"## Claim 111, {title}: {len(X)} fundable of {len(R)}; exact {sum(x['exact'] for x in X)}")
        print(f"- part 1: lower bound {sum(x['lower'] <= x['Lam'] + 1e-9 for x in X)}/{len(X)} (worst excess {max(x['lower'] - x['Lam'] for x in X):.1e}); "
              f"Lambda <= min(s'(w_J - w_1), s'Sigma^-1 s/(2 gamma)) {sum(x['Lam'] <= min(x['up1'], x['up2']) + 1e-9 for x in X)}/{len(X)} (worst {max(x['Lam'] - min(x['up1'], x['up2']) for x in X):.1e}); "
              f"||w_J - w_1|| <= ||s||/gamma {sum(x['wgap'] <= x['snorm'] + 1e-7 for x in X)}/{len(X)}")
        print(f"  - which upper bound binds: s'(w_J - w_1) smaller at {sum(x['up1'] < x['up2'] for x in X)}; median Lambda / min bound over inexact "
              f"{sorted(x['Lam'] / min(x['up1'], x['up2']) for x in X if not x['exact'])[len([x for x in X if not x['exact']]) // 2] if any(not x['exact'] for x in X) else float('nan'):.2f}")
        s0 = [max(abs(v) for v in x["s_dual"]) <= 1e-7 for x in X]
        print(f"- part 2: s = 0 (1e-7) and inexact {sum(z and not x['exact'] for z, x in zip(s0, X))}; s = 0 and exact {sum(z and x['exact'] for z, x in zip(s0, X))}; "
              f"s's dual against its definition at ETFs traded to an interior holding: {max([abs(x['s_dual'][int(j)] - v) for x in X for j, v in x['s_def'].items()] + [0]):.1e}")
        U = [x for x in X if x["exact"] and x["s_def"] and x["k2"] > 1e-9 and x["eta2"] <= 1e-9]
        K = [x for x in X if x["exact"] and x["s_def"] and x["k2"] > 1e-9 and x["eta2"] > 1e-9]
        print(f"  - exact splits with a traded interior ETF and a slack fibre budget (unique multipliers): {len(U)}, largest |s_j| there {max([abs(v) for x in U for v in x['s_def'].values()] + [0]):.1e}; "
              f"set aside with k2 > 1e-9 but eta2 > 1e-9 (binding within tolerance; Deviation 2): {len(K)}")
        if nm == "aware":
            print(f"- 3a: every fund held at x_1 at {sum(x['held'] for x in X)}; of those exact with x_1 = x_J {sum(x['held'] and x['exact'] and x['x1_is_J'] for x in X)}")
            print(f"- 3b: hypotheses met at {sum(x['c3b'] for x in X)}; exact {sum(x['c3b'] and x['exact'] for x in X)}; s = 0 {sum(x['c3b'] and max(abs(v) for v in x['s_dual']) <= 1e-7 for x in X)}")
            C = [x for x in X if x["c3c"]]
            print(f"- 3c: hypotheses met at {len(C)}: s_T = 0 to {max([x['sT'] for x in C] + [0]):.1e}; Q_F(x^A_2 - x^A-) = 0 to {max([x['QF'] for x in C] + [0]):.1e}; "
                  f"exact iff the fund lines hold with stage 1's ETF marginals {sum(x['lines3c'] == x['exact'] for x in C)}/{len(C)} ({sum(x['exact'] for x in C)} exact)")
            print(f"- stage-1 statuses: {dict(Counter(x['st1'] for x in X).most_common(8))}")
        print()
    both = [(r["aware"], r["041"]) for r in R if r["041"] is not None]
    print(f"## Part 4: on the {len(both)} draws where both are fundable, exact: incumbent-aware {sum(a['exact'] for a, b in both)}, claim 041's {sum(b['exact'] for a, b in both)}; "
          f"incumbent-aware loss <= claim 041's at {sum(a['Lam'] <= b['Lam'] + 1e-12 for a, b in both)}")
    print(f"\n- seconds {S['seconds']:.0f}")


if __name__ == "__main__":
    main()
