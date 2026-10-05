"""Experiment 026 report: claim 100's checks (uv run python experiments/026/report.py)."""
import json
import statistics
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent


def main():
    R = json.load(open(HERE / "results.json"))
    by = {(c["inst"], c["T"], c["kappa"], c["returns"], round(1 / c["h"])): c for c in R}
    ceil_v = 0; mono_v = 0; d2_v = 0
    print("## Per cell (h = 1/400; widths as fractions of the static width; medians over belief points with an interior band)\n")
    print("| instrument | T | kappa (bp) | returns | width/static at t = 0 / mid / T-2 / T-1 | coarse points (t <= T-2) | "
          "pure-learning t_0 | innovation sd / static at t = 0 / T-2 | drift / static at t = 0 / T-2 | resolved (h 1/200 vs 1/400) |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for (inst, T, k, ret, H), c in sorted(by.items(), key=lambda kv: (kv[0][0], kv[0][1], kv[0][2], kv[0][3])):
        if H != 400:
            continue
        h = c["h"]
        sw = c["static_widths"]
        mono_v += sum(1 for a, b in zip(sw, sw[1:]) if b < a - 1e-15)
        rs = [r for r in c["records"] if r["interior"]]
        for r in rs:
            if r["width"] > r["static"] + 2 * h:
                ceil_v += 1
        coarse = [r for r in rs if r["t"] <= T - 2 and abs(r["width"] - r["static"]) <= 2 * h]
        if not ret:
            d2_v += sum(1 for r in coarse if r.get("n_nodes_below_bound", 0) > 0)
        med = {}
        for t in range(T):
            ws = [r["width"] / r["static"] for r in rs if r["t"] == t]
            med[t] = statistics.median(ws) if ws else None
        # pure learning: first t_0 from which every interior band (t <= T-2) is narrower by more than 2h
        t0 = None
        if not ret:
            for cand in range(T - 1):
                if all(r["width"] < r["static"] - 2 * h for r in rs if cand <= r["t"] <= T - 2):
                    t0 = cand
                    break
        c2 = by[(inst, T, k, ret, 200)]
        m2 = {(r["t"], r["j"]): r["width"] for r in c2["records"] if r["interior"]}
        res = [abs(m2[(r["t"], r["j"])] - r["width"]) < 0.1 * r["width"] for r in rs if (r["t"], r["j"]) in m2 and r["width"] >= 3 * h]
        sd0 = statistics.median([r["sd_move"] / r["static"] for r in rs if r["t"] == 0]) if any(r["t"] == 0 for r in rs) else float("nan")
        sdl = statistics.median([r["sd_move"] / r["static"] for r in rs if r["t"] == T - 2]) if any(r["t"] == T - 2 for r in rs) else float("nan")
        dr0 = statistics.median([r["drift"] / r["static"] for r in rs if r["t"] == 0]) if any(r["t"] == 0 for r in rs) else float("nan")
        drl = statistics.median([r["drift"] / r["static"] for r in rs if r["t"] == T - 2]) if any(r["t"] == T - 2 for r in rs) else float("nan")
        f = lambda v: "-" if v is None else f"{v:.3f}"  # noqa: E731
        print(f"| {inst} | {T} | {k * 1e4:.0f} | {'on' if ret else 'off'} | {f(med.get(0))} / {f(med.get(T // 2))} / {f(med.get(T - 2))} / "
              f"{f(med.get(T - 1))} | {len(coarse)} | {'-' if ret else (t0 if t0 is not None else 'none')} | {sd0:.3f} / {sdl:.3f} | "
              f"{dr0:+.4f} / {drl:+.4f} | {sum(res)}/{len(res)} |")
    print(f"\n**Claim 100 checks (h = 1/400):** ceiling violations (width > static + 2h): {ceil_v}; static width decreasing "
          f"anywhere: {mono_v}; part 2d violations (returns off; a coarse band with a quadrature target move below the side-weight "
          f"bound): {d2_v}")
    print("\n**Static width by quarter (h-independent; T = 20; bp values are the rate):**\n")
    print("| instrument | kappa (bp) | t = 0 | t = 5 | t = 10 | t = 19 | limit 2 kappa / (gamma Sigma_r) |")
    print("|---|---|---|---|---|---|---|")
    for inst in ("fund", "etf"):
        for k in (0.0005, 0.002, 0.01):
            c = by[(inst, 20, k, False, 400)]
            sw = c["static_widths"]
            sres = 0.02 if inst == "fund" else 0.002
            lim = 2 * k / (5.0 * (0.0854 ** 2 + sres ** 2))
            print(f"| {inst} | {k * 1e4:.0f} | {sw[0]:.5f} | {sw[5]:.5f} | {sw[10]:.5f} | {sw[19]:.5f} | {lim:.5f} |")


if __name__ == "__main__":
    main()
