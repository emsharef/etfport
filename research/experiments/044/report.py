"""Experiment 044 report (uv run python experiments/044/report.py), from summary.json."""
import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent


def main():
    S = json.load(open(HERE / "summary.json")); R = S["rows"]; B = [r for r in R if not r["edge"]]
    print(f"{len(R)} draws (500 N = 3, 500 one fund); {S['statement']}; binding budget at {sum(r['binding'] for r in R)}; knife edges {len(R) - len(B)}")
    print(f"- solvers: CLARABEL against OSQP, objective {max(r['dis'] for r in R):.1e}, holdings {max(r['dx'] for r in R):.1e}\n")
    P = [r["p2"] for r in B]
    print("## Part 2 (at the solver's optimum, given its statuses)")
    print(f"- statuses (ETF 1, ETF 2): {dict(Counter(p['st'] for p in P).most_common())}")
    for k, nm in (("e2a", "2a traded exposure w_T"), ("e2b", "2b fixed ETFs' marginals g_F"), ("e2c", "2c fund marginal G_i"), ("line", "fund line with box signs")):
        v = [p[k] for p in P if p.get(k) is not None]
        print(f"- {nm}: {len(v)} draws, largest |difference| {max(v):.1e}")
    print(f"- at-zero slacks: smallest {min(p['zeta_min'] for p in P if p.get('zeta_min') is not None):.1e}; idle marginals inside their bands, smallest margin "
          f"{min(p['idle_min'] for p in P if p.get('idle_min') is not None):.1e} ({sum(p.get('idle_min') is not None for p in P)} draws with an idle ETF)")
    D = [d for p in P for d in p["d"]]
    print(f"- 2d over {len(D)} ETFs starting at zero ({dict(Counter(d['st'] for d in D))}): at zero with g > threshold {sum(d['st'] == 'Z' and d['g'] > d['th'] + 1e-9 for d in D)}; "
          f"bought with g != threshold {sum(d['st'] == 'B' and abs(d['g'] - d['th']) > 1e-9 for d in D)}; g < threshold but not at zero {sum(d['g'] < d['th'] - 1e-9 and d['st'] != 'Z' for d in D)}; "
          f"one-quantity test against the status: {sum((d['st'] == 'Z') == (d['gown'] <= d['th'] + 1e-9) for d in D)}/{len(D)}\n")
    Fb = [r for r in B if r["fibre"] is not None]; E = [r for r in Fb if r["fibre"]["exact"]]
    print("## Part 4")
    print(f"- fibre-confined: fundable fibre at {len(Fb)} of {len(B)} (claim 041's w* needs more cash than h^- at the rest); exact at {len(E)}")
    print(f"- 4a criterion (LP in (eta, s), violation <= 1e-6) against exactness on holdings: {sum(r['fibre']['exact'] == r['fibre']['crit'] for r in Fb)}/{len(Fb)}")
    print(f"- 4b: exact cases by the stage-2 ETF moves: {dict(Counter(tuple(sorted(r['fibre']['moves'])) for r in E))}; with a binding budget {sum(r['binding'] for r in E)}; "
          f"with an ETF bought to an interior holding {sum('bought_interior' in r['fibre']['moves'] for r in E)}; sold to an interior holding {sum('sold_interior' in r['fibre']['moves'] for r in E)}; "
          f"with a sale to zero {sum('sold_to_zero' in r['fibre']['moves'] for r in E)}")
    I = [r for r in Fb if not r["fibre"]["exact"]]
    print(f"- inexact cases with an ETF traded to an interior holding: {sum(any(m in ('bought_interior', 'sold_interior') for m in r['fibre']['moves']) for r in I)}/{len(I)}; "
          f"exact among fundable draws where stage 2 trades an ETF to an interior holding: {sum(any(m in ('bought_interior', 'sold_interior') for m in r['fibre']['moves']) for r in E)}")
    So = [r["soft"] for r in B if r.get("soft")]
    print(f"- 4c: unconstrained stage 1, largest |Lambda_s| {max(abs(r['Lam_s_free']) for r in B):.1e}; R_E = W_F: 0 <= Lambda_s <= zeta*'(w_s2 - w_J) at "
          f"{sum(-1e-9 <= s['Lam_s'] <= s['bound'] + 1e-9 for s in So)}/{len(So)}, exact iff x_J solves the tilted stage 2 at {sum(s['exact'] == s['joint_solves'] for s in So)}/{len(So)} "
          f"({sum(s['exact'] for s in So)} exact, of which zeta* = 0 at {sum(s['exact'] and s['zeta_norm'] < 1e-9 for s in So)}; zeta* = 0 and inexact {sum(not s['exact'] and s['zeta_norm'] < 1e-9 for s in So)})")
    print(f"\n- seconds {S['seconds']:.0f}")


if __name__ == "__main__":
    main()
