"""Experiment 026, Deviation 2 (PM's scope note, received after the full run): the two points PM scoped 026 to.
(a) Which instruments of experiment 024's calibration (M5/M7: 30 funds, 8 ETFs, 5 French factors, pooled prior;
    experiments/022/model.py) start in the fine regime at D13's corrected crossover: an instrument is fine from the
    first review when its initial belief-innovation sd in return units, sqrt((G V_0 G')_ii) with V_0 = P_0 - P_1, is
    below its round-trip cost over root six. Rates: 024's band variant (fund 100 bp, ETF 5 bp each way) and the
    sweep {5, 20, 100} bp each way; also the crossover quarter, the first t with sqrt((G V_t G')_ii) below the threshold.
(b) How long cheap ETFs (5 bp) stay at the static ceiling in 026's single-instrument cells, returns on and off: per
    quarter, the share of interior belief points whose width is within 2h of the static width.
Run: uv run python experiments/026/scope.py
"""
import importlib.util
import json
import math
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
_s = importlib.util.spec_from_file_location("m022", ROOT / "experiments" / "022" / "model.py")
m022 = importlib.util.module_from_spec(_s); _s.loader.exec_module(m022)


def part_a():
    I = m022.Inst(T=120)
    sd = lambda t: np.sqrt(np.clip(np.diag(I.G @ I.Q(t) @ I.G.T), 0, None))  # noqa: E731
    s0 = sd(0)
    print("## (a) Experiment 024's calibration: initial belief-innovation sd against round-trip / sqrt(6)\n")
    print(f"initial belief-innovation sd (bp per quarter): funds median {np.median(s0[:I.N]) * 1e4:.2f} "
          f"(range {s0[:I.N].min() * 1e4:.2f}-{s0[:I.N].max() * 1e4:.2f}); ETFs {', '.join(f'{v * 1e4:.2f}' for v in s0[I.N:])}\n")
    print("| rate each way (bp) | threshold round-trip/sqrt(6) (bp) | funds fine from t = 0 | ETFs fine from t = 0 | "
          "latest crossover quarter among the rest (T = 120) |")
    print("|---|---|---|---|---|")
    out = {}
    for k in (5, 20, 100):
        thr = 2 * k * 1e-4 / math.sqrt(6)
        ff = int((s0[:I.N] < thr).sum()); fe = int((s0[I.N:] < thr).sum())
        cross = []
        for i in range(I.n):
            if s0[i] >= thr:
                t = next((t for t in range(120) if sd(t)[i] < thr), None)
                cross.append(t)
        latest = max((c for c in cross if c is not None), default=None)
        never = sum(c is None for c in cross)
        print(f"| {k} | {thr * 1e4:.2f} | {ff}/30 | {fe}/8 | {latest if latest is not None else '-'}"
              f"{f' ({never} not within 120)' if never else ''} |")
        out[k] = dict(threshold_bp=thr * 1e4, funds_fine=ff, etfs_fine=fe, latest_crossover=latest, never=never)
    print("\n024's band variant: funds at 100 bp each way use the 100 bp row; ETFs at 5 bp use the 5 bp row.")
    return dict(sd0_bp=(s0 * 1e4).tolist(), rows=out)


def part_b():
    R = json.load(open(HERE / "results.json"))
    print("\n## (b) Cheap ETFs (5 bp) at the static ceiling, 026's single-instrument cells (h = 1/400)\n")
    print("| T | returns | share of interior belief points at the ceiling, by quarter (t = 0, 1, ...) | last quarter with any at the ceiling (t <= T-2) |")
    print("|---|---|---|---|")
    out = {}
    for c in R:
        if c["inst"] != "etf" or abs(c["kappa"] - 0.0005) > 1e-12 or abs(c["h"] - 1 / 400) > 1e-12:
            continue
        T, h = c["T"], c["h"]
        shares, last = [], None
        for t in range(T - 1):
            rs = [r for r in c["records"] if r["t"] == t and r["interior"]]
            at = [r for r in rs if abs(r["width"] - r["static"]) <= 2 * h]
            shares.append(len(at) / len(rs) if rs else float("nan"))
            if at:
                last = t
        print(f"| {T} | {'on' if c['returns'] else 'off'} | {', '.join(f'{s:.2f}' for s in shares)} | {last if last is not None else 'none'} |")
        out[f"T{T}_{'on' if c['returns'] else 'off'}"] = dict(shares=shares, last=last)
    return out


if __name__ == "__main__":
    a = part_a(); b = part_b()
    (HERE / "scope.json").write_text(json.dumps(dict(crossover=a, etf_ceiling=b)))
