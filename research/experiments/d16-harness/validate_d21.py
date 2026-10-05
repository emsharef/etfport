"""Validation of harness.m8_model (D21 preparation; PM's D19 note, item 2): at experiment 048's 72 cells, the new constructor
reproduces 048's dynamic values and root holdings, whether the alpha prior is given by its SD, by the filter's gain, or by
the revision variance, and whether the fund rate is given directly or as a cost ratio. Run:
uv run python experiments/d16-harness/validate_d21.py"""
import importlib.util
import itertools
import json
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from harness import m8_model  # noqa: E402

_p = importlib.util.spec_from_file_location("presets", HERE.parent / "presets.py"); PR = importlib.util.module_from_spec(_p); _p.loader.exec_module(PR)


def main():
    C = {(c["regime"], tuple(c["start"]), c["cash"], c["unc"], c["costmul"]): c for c in json.load(open(HERE.parent / "048" / "summary.json"))["cells"]}
    worst = dict(value=0.0, x0=0.0); modes_worst = 0.0
    for key, c in C.items():
        rg, st, ca, un, cm = key; P = PR.PRESETS[rg]
        asd = P["alpha_sd"] * un; s2 = P["sigma_A"] ** 2; pa = asd ** 2
        common = dict(bA=1.0, bE=1.0, cE=P["etf_fee"], lam=P["premium"][0], alpha=P["alpha_mean"], premium_sd=P["premium_sd"][0] * un,
                      sigma_f=P["factor_sd"][0], sigma_A=P["sigma_A"], gamma=P["gamma"], beta=1.0, etf_rate=P["etf_rate"], capA=P["fund_cap"], observe_factor=False)
        variants = [m8_model(alpha_sd=asd, fund_rate=P["fund_rate"] * cm, **common),
                    m8_model(alpha_gain=pa / (pa + s2), cost_ratio=P["fund_rate"] * cm / P["etf_rate"], **common),
                    m8_model(alpha_revision_var=pa ** 2 / (pa + s2), fund_rate=P["fund_rate"] * cm, **common)]
        sols = [M.solve(np.array(st, float), ca, T=2) for M in variants]
        worst["value"] = max(worst["value"], abs(sols[0]["value"] - c["dynamic"]["value"]))
        worst["x0"] = max(worst["x0"], float(np.max(np.abs(sols[0]["x"][0][0] - np.array(c["dynamic"]["x0"])))))
        for s in sols[1:]:
            modes_worst = max(modes_worst, abs(s["value"] - sols[0]["value"]), float(np.max(np.abs(s["x"][0][0] - sols[0]["x"][0][0]))))
    json.dump(dict(worst_vs_048=worst, worst_between_modes=modes_worst), open(HERE / "validation_d21.json", "w"), indent=1)
    print(f"against experiment 048 (72 cells): value {worst['value']:.1e}, root holdings {worst['x0']:.1e}; between the SD, gain and revision-variance inputs and the cost-ratio input: {modes_worst:.1e}")


if __name__ == "__main__":
    main()
