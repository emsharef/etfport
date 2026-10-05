"""Experiment 023, Deviation 4 (after the report; mathb's note 2026-09-28-exp023-sections).
(1) From Part A's committed partA.json (P1, h = 1/400): the ETF's no-trade-set section width against claim 029 part
    2c's two last-review faces, the ETF's own face (kappa^+_E + kappa^-_E)/(gamma S_EE) and the fund's face
    (kappa^+_A + kappa^-_A)/(gamma |S_AE|), by fund rate and quarter, beside the exact 2c section at the same S_t.
(2) One-instrument ETF cells (N = 0, M = 1, K = 1; premium learning drives the target), solved with Part A's solver:
    T in {4, 8, 20}, kappa_E in {5, 20} bp, h = 1/400; band width against the static width by quarter.
Run: uv run python experiments/023/sections.py   (writes experiments/023/sections.json and prints both tables)
"""
import json
import statistics
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import partA  # noqa: E402
from model import Inst  # noqa: E402  (experiment 021's, via partA's path)


def faces_table():
    R = json.load(open(HERE / "partA.json"))
    print("## (1) P1: ETF no-trade-set section against claim 029 part 2c's faces (h = 1/400; medians over belief points)\n")
    print("| fund rate (bp) | T | t | ETF section width | ETF own face | fund face (2 kappa_A / gamma abs(S_AE)) | exact 2c section at S_t | "
          "tighter face | section / tighter face |")
    print("|---|---|---|---|---|---|---|---|---|")
    rows = []
    for c in R:
        if c["inst"] != "P1" or abs(c["h"] - 1 / 400) > 1e-12:
            continue
        I = Inst("P1", *partA.SPECS["P1"], partA.GAMMA, c["T"])
        for t in sorted({r["t"] for r in c["records"]}):
            rs = [r for r in c["records"] if r["inst"] == 1 and r["t"] == t and r["nt_interior"] and r["nt_width"] is not None]
            if not rs:
                continue
            S = I.S(t)
            own = 2 * c["kappa_etf"] / (partA.GAMMA * S[1, 1])
            fund = 2 * c["kappa_fund"] / (partA.GAMMA * abs(S[0, 1]))
            w = statistics.median([r["nt_width"] for r in rs]); sec = statistics.median([r["section"] for r in rs])
            tight = min(own, fund)
            rows.append(dict(kappa_fund=c["kappa_fund"], T=c["T"], t=t, width=w, own=own, fund=fund, section=sec))
            if t in (0, c["T"] // 2, c["T"] - 2, c["T"] - 1):
                print(f"| {c['kappa_fund'] * 1e4:.0f} | {c['T']} | {t} | {w:.4f} | {own:.4f} | {fund:.4f} | {sec:.4f} | "
                      f"{'fund' if fund < own else 'ETF'} | {w / tight:.3f} |")
    return rows


def etf_alone():
    partA.SPECS["E1"] = (0, 1, 1, [], True)
    print("\n## (2) ETF alone (N = 0, M = 1, K = 1; premium learning; h = 1/400)\n")
    print("| kappa_E (bp) | T | t | band width (median over belief points) | static width | width / static | innovation sd / static |")
    print("|---|---|---|---|---|---|---|")
    out = []
    for ke in (0.0005, 0.002):
        for T in (4, 8, 20):
            r = partA.solve("E1", 0.0, ke, T, 1 / 400)
            for t in sorted({x["t"] for x in r["records"]}):
                rs = [x for x in r["records"] if x["t"] == t and x["nt_interior"] and x["nt_width"] is not None]
                if not rs:
                    continue
                w = statistics.median([x["nt_width"] for x in rs]); st = rs[0]["static"]
                s = statistics.median([x["sd_innov"] for x in rs])
                out.append(dict(kappa_etf=ke, T=T, t=t, width=w, static=st, sd=s))
                if t in (0, T // 2, T - 2, T - 1):
                    print(f"| {ke * 1e4:.0f} | {T} | {t} | {w:.4f} | {st:.4f} | {w / st:.3f} | {s / st:.2f} |")
    return out


if __name__ == "__main__":
    a = faces_table()
    b = etf_alone()
    (HERE / "sections.json").write_text(json.dumps(dict(faces=a, etf_alone=b)))
