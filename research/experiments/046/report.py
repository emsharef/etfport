"""Experiment 046 report (uv run python experiments/046/report.py), from summary.json."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def scaled(c):
    """Bounds with each term scaled by its own one-instrument gain ratio (Deviation 2)."""
    rA, rE = c["rA"], c["rE"]
    return dict(up=rA * c["aA_up"] + rE * c["aE"], lo_disp=(rA * c["aA_lo"] + rE * c["aE"]) if c["aA_lo"] is not None else None,
                lo_gen=rA * c["gen_A"] + rE * c["gen_E"], lo_b=rE * c["lo_b"], dec=rA * c["aA"] + rE * c["aE"])


def main():
    S = json.load(open(HERE / "summary.json")); C = S["cells"]
    print(S["statement"], "\n")
    print("a_b's term is scaled by r_E, the ETF's ratio (only the ETF moves the ETF's own gap)")
    print("| part | corr | xi | eps | r | eps_E | r_A | r_E | resolved | a / upper | a / lower (displayed) | a / lower (general) | a / a_b | position | converged |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    fails = []
    for c in sorted(C, key=lambda c: (c["part"], c["corr"], c["xi"], -c["eps"], c["r"])):
        b = scaled(c); res = abs(1 - c["rA"]) <= 0.02 and abs(1 - c["rE"]) <= 0.02; tol = 2 * max(abs(1 - c["rA"]), abs(1 - c["rE"]))
        lo = max(b["lo_gen"], b["lo_b"]); pos = (c["a"] - b["lo_gen"]) / (b["up"] - b["lo_gen"]) if b["up"] > b["lo_gen"] else float("nan")
        ok = c["a"] <= b["up"] * (1 + tol) and c["a"] >= lo * (1 - tol)
        if res and not ok:
            fails.append(c)
        print(f"| {c['part']} | {c['corr']} | {c['xi']} | {c['eps']} | {c['r']} | {c['epsE']:.2f} | {c['rA']:.4f} | {c['rE']:.4f} | {'yes' if res else 'no'} | {c['a'] / b['up']:.4f} | "
              f"{(c['a'] / b['lo_disp']) if b['lo_disp'] else float('nan'):.4f} | {c['a'] / b['lo_gen']:.4f} | {c['a'] / b['lo_b']:.3f} | {pos:.2f} | {c['converged']} ({c['iters']}) |")
    print(f"\n- resolved cells: {sum(abs(1 - c['rA']) <= 0.02 and abs(1 - c['rE']) <= 0.02 for c in C)} of {len(C)}; outside the sandwich beyond tolerance: {len(fails)}")
    P2 = [c for c in C if c["part"] == "2"]
    print(f"- part 2 (Sigma_AE = 0): a / (r_A a_A + r_E a_E) = {', '.join(f'{c['a'] / scaled(c)['dec']:.6f}' for c in P2)}")
    print(f"- part 3 identity (floating point): largest error {max(c['gap_err'] for c in C if c['gap_err'] is not None):.1e}; gap bound holds at {sum(c['gap_bound_ok'] for c in C if c['gap_bound_ok'] is not None)}")
    P4 = sorted([c for c in C if c["part"] == "4c"], key=lambda c: c["xi"])
    print(f"- part 4(c) (corr 0.9, eps 0.2): xi, a, a_b, a/a_b: {[(c['xi'], f'{c['a']:.3e}', f'{c['lo_b']:.3e}', round(c['a'] / c['lo_b'], 3)) for c in P4]}")
    print(f"- seconds {S['seconds']:.0f}")


if __name__ == "__main__":
    main()
