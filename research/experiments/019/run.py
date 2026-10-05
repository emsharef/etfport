"""Experiment 019 (D4): two-stage versus joint under estimated forecasts, and the scaling of 018's exact gap.
Registered design: experiments/019-m2-two-stage-estimated.md.

Part E reuses experiment 006's Part M estimation design (`estimates`, grid, seeds (2006, T, r), R = 2000) and
experiment 018's two-stage procedure (stage 1 over the implementable set R0 = conv{0, loading rows}, alpha-aware
stage 2), both with the plug-in estimates. Part S reads experiment 018's committed exact results.

Run:    uv run python experiments/019/run.py          (Part E; writes experiments/019/results.json)
Report: uv run python experiments/019/run.py report   (Part E tables and Part S fits)
"""
from __future__ import annotations

import importlib.util
import itertools
import json
import math
import os
import statistics
import sys
import time
from dataclasses import replace
from fractions import Fraction as Fr
from multiprocessing import Pool
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


e006 = _load("e006", ROOT / "experiments" / "006" / "run.py")
e018 = _load("e018", ROOT / "experiments" / "018" / "run.py")
from m2 import Instance2, mean_vector, objective, sigma_formula, solve  # noqa: E402  (path set by e006)


def stage1_float(lam, gamma, rows, sf):
    """Float version of 018's stage 1 with premia lam (estimated): max lam'b - (gamma/2) b'Sf b over conv{0, rows}."""
    P = [(0.0, 0.0)] + [tuple(float(x) for x in r) for r in rows]
    s2 = [float(x) ** 2 for x in sf]
    g = lambda b: sum(lam[k] * b[k] for k in range(2)) - gamma / 2 * sum(s2[k] * b[k] ** 2 for k in range(2))  # noqa: E731
    bu = tuple(lam[k] / (gamma * s2[k]) for k in range(2))
    cands = list(P)
    for A, B_ in itertools.combinations(P, 2):
        d = (B_[0] - A[0], B_[1] - A[1])
        den = gamma * sum(s2[k] * d[k] ** 2 for k in range(2))
        if den > 0:
            t = min(max(sum((lam[k] - gamma * s2[k] * A[k]) * d[k] for k in range(2)) / den, 0.0), 1.0)
            cands.append((A[0] + t * d[0], A[1] + t * d[1]))
    # interior optimum if b_u lies in the hull (exact test on floats via 018's routine)
    if e018.in_hull(tuple(Fr(x) for x in bu), [tuple(Fr(x) for x in p) for p in P]):
        return bu, False
    return max(cands, key=g), True


def two_stage(I, lam, alpha):
    """018's 2S-alpha with plug-in (lam, alpha): stage-2 mean gamma B Sf b* + alpha e_A - c^E."""
    rows = [I.BA] + list(I.BE)
    b, _ = stage1_float(lam, float(I.gamma), rows, I.sf)
    lam2 = tuple(float(I.gamma) * float(I.sf[k]) ** 2 * b[k] for k in range(2))
    J = replace(I, lam=lam2, alpha=alpha)
    return solve(J, "F", exact=False)[1]


def cell(key):
    geom, cost, alpha, info, T = key
    I = e006.instance(geom, cost, Fr(alpha), e006.M_GAMMA, e006.M_SA, e006.M_START)
    S = [[float(x) for x in r] for r in sigma_formula(I)]
    mu = [float(x) for x in mean_vector(I)]
    VF = float(solve(I, "F")[0])
    Q = lambda w: float(objective(I, S, mu, w))  # noqa: E731
    reg = {p: [] for p in ("2S", "JP", "EP")}
    D, W = [], {"2S>JP": 0, "JP>2S": 0, "tie": 0}
    for r in range(e006.R):
        rng = np.random.default_rng([2006, T, r])          # 006's common random numbers
        lam, al = e006.estimates(I, info, T, rng)
        Ih = replace(I, lam=lam, alpha=al)
        wE = solve(Ih, "E", exact=False)[1]
        wJ = solve(Ih, "F", exact=False)[1]
        w2 = two_stage(I, lam, al)
        q2, qJ, qE = Q(w2), Q(wJ), Q(wE)
        reg["2S"].append(VF - q2); reg["JP"].append(VF - qJ); reg["EP"].append(VF - qE)
        D.append(q2 - qJ)
        W["tie" if abs(q2 - qJ) <= 1e-12 else "2S>JP" if q2 > qJ else "JP>2S"] += 1
    m = lambda x: (float(np.mean(x)), float(np.std(x, ddof=1) / math.sqrt(len(x))))  # noqa: E731
    return dict(geom=geom, cost=cost, alpha=alpha, info=info, T=T, reg={p: m(v) for p, v in reg.items()},
                D=m(D), wins={k: v / e006.R for k, v in W.items()})


def keys():
    return [(g, c, str(a), i, T) for g, c, a, i, T in
            itertools.product(e006.GEOMETRY, e006.M_COSTS, e006.M_ALPHA, e006.M_INFO, e006.M_T)]


def run():
    t0 = time.time()
    with Pool(int(os.environ.get("PROCS", "8"))) as pool:
        rows = pool.map(cell, keys(), chunksize=1)
    (HERE / "results.json").write_text(json.dumps(rows, indent=0))
    print(f"{len(rows)} cells, seconds: {time.time() - t0:.0f}")


def part_s():
    """Scaling of 018's exact 2S-alpha gap with stage 1's multiplier and the constraints' slack."""
    rows = json.load(open(ROOT / "experiments" / "018" / "results.json"))
    out = []
    for r in rows:
        I = e018.instance(r["geom"], r["cost"], Fr(r["alpha"]), Fr(r["gamma"]), Fr(r["sA"]), r["start"])
        b = [Fr(x) for x in r["bstar"]]
        nu = [e018.LAM[k] - I.gamma * e018.SF[k] ** 2 * b[k] for k in range(2)]      # stage-1 multiplier vector
        wJ = [Fr(x) for x in r["wJ"]]; w2 = [Fr(x) for x in r["2S-alpha"]["w"]]
        eJ, e2 = e018.expo(I, wJ), e018.expo(I, w2)
        de = [eJ[k] - e2[k] for k in range(2)]
        Sig = sigma_formula(I)
        dw = [wJ[i] - w2[i] for i in range(I.d)]
        quad = I.gamma / 2 * sum(dw[i] * Sig[i][j] * dw[j] for i in range(I.d) for j in range(I.d))
        lin = sum(nu[k] * de[k] for k in range(2))
        v2 = [w2[i] - I.w0[i] for i in range(I.d)]
        out.append(dict(r=r, gap=Fr(r["2S-alpha"]["gap"]), lin=lin, quad=quad,
                        nu=math.sqrt(sum(float(x) ** 2 for x in nu)),
                        dist=math.sqrt(sum(float(x) ** 2 for x in de)),
                        slack_fund=float(I.k0 - sum(v2) - e018.tau(I, v2)), slack_long=float(min(w2)),
                        slack_cap=float(min(1 - x for x in w2))))
    return out


def report():
    rows = json.load(open(HERE / "results.json"))
    bp = 1e4
    print("## Part E: estimated forecasts (gamma 5, active residual 2%, start S1, R = 2000, CRN)\n")
    print("Regret = V_F(theta) - Q(w; theta), bp per quarter, MC mean (SE). D = Q(2S) - Q(JP), paired.\n")
    print("| geometry | costs | alpha (bp) | estimated | T | regret 2S | regret joint plug-in | regret ETF-only plug-in | "
          "D mean (SE) | P(2S better) | P(JP better) | P(tie) | verdict |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    f = lambda t: f"{t[0] * bp:.3f} ({t[1] * bp:.3f})"  # noqa: E731
    cnt = {"2S better": 0, "JP better": 0, "tie": 0}
    for o in rows:
        d, s = o["D"]
        v = "2S better" if d - 2 * s > 0 else "JP better" if d + 2 * s < 0 else "tie"
        o["v"] = v
        cnt[v] += 1
        print(f"| {o['geom']} | {o['cost']} | {float(Fr(o['alpha'])) * 1e4:.0f} | {o['info']} | {o['T']} | {f(o['reg']['2S'])} | "
              f"{f(o['reg']['JP'])} | {f(o['reg']['EP'])} | {f(o['D'])} | {o['wins']['2S>JP']:.3f} | {o['wins']['JP>2S']:.3f} | "
              f"{o['wins']['tie']:.3f} | {v} |")
    print(f"\nverdicts (mean D beyond 2 SE): {cnt}; cells with SE(D) > 0.1 bp: {sum(o['D'][1] * bp > 0.1 for o in rows)}")
    for key in ("geom", "cost", "alpha", "info", "T"):
        print(f"**by {key}**: " + "; ".join(
            f"{v}: " + ", ".join(f"{k} {sum(1 for o in rows if o[key] == v and o['v'] == k)}" for k in cnt)
            + f", median D {statistics.median([o['D'][0] * bp for o in rows if o[key] == v]):+.3f} bp"
            for v in sorted({o[key] for o in rows}, key=str)))
    print(f"median regret: 2S {statistics.median([o['reg']['2S'][0] * bp for o in rows]):.3f}, "
          f"JP {statistics.median([o['reg']['JP'][0] * bp for o in rows]):.3f}, EP {statistics.median([o['reg']['EP'][0] * bp for o in rows]):.3f} bp")

    print("\n## Part S: scaling of 018's exact 2S-alpha gap\n")
    S = part_s()
    pos = [s for s in S if s["gap"] > 0]
    print(f"cells {len(S)}; gap > 0 in {len(pos)}")
    print(f"- identity gap = nu'(e_J - e_2S) + f2_term with f2_term <= 0: gap <= nu'(e_J - e_2S) holds in "
          f"{sum(s['gap'] <= s['lin'] for s in S)} of {len(S)}")
    ex = sum(s["gap"] == s["lin"] - s["quad"] for s in S)
    print(f"- gap == nu'(Delta e) - (gamma/2) Delta w' Sigma Delta w exactly in {ex} of {len(S)} "
          f"(exact when the stage-2 optimum is an interior stationary point of f2 relative to w_J's direction)")
    rl = [float(s["gap"] / s["lin"]) for s in pos if s["lin"] > 0]
    print(f"- linear bound ratio gap / (nu' Delta e): min {min(rl):.3f}, median {statistics.median(rl):.3f}, max {max(rl):.3f}")
    rq = [float(s["gap"] / s["quad"]) for s in pos if s["quad"] > 0]
    print(f"- quadratic ratio gap / ((gamma/2) Delta w' Sigma Delta w): min {min(rq):.3f}, median {statistics.median(rq):.3f}, max {max(rq):.3f}")
    rn = [float(s["gap"]) / (s["nu"] * s["dist"]) for s in pos if s["nu"] * s["dist"] > 0]
    print(f"- norm bound ratio gap / (|nu| |Delta e|): min {min(rn):.3f}, median {statistics.median(rn):.3f}, max {max(rn):.3f}")
    x = np.log([s["dist"] for s in pos if s["dist"] > 0]); y = np.log([float(s["gap"]) for s in pos if s["dist"] > 0])
    xn = np.log([s["nu"] * s["dist"] for s in pos if s["dist"] > 0])
    print(f"- log-log slope of gap on |Delta e|: {np.polyfit(x, y, 1)[0]:.3f}; on |nu||Delta e|: {np.polyfit(xn, y, 1)[0]:.3f} "
          f"(1 = linear, 2 = quadratic); cells {len(x)}")
    z = [s for s in S if s["gap"] == 0]
    print(f"- slack at the two-stage solution, gap = 0 vs gap > 0 (medians): funding {statistics.median([s['slack_fund'] for s in z]):.4f} vs "
          f"{statistics.median([s['slack_fund'] for s in pos]):.4f}; long-only {statistics.median([s['slack_long'] for s in z]):.4f} vs "
          f"{statistics.median([s['slack_long'] for s in pos]):.4f}; cap {statistics.median([s['slack_cap'] for s in z]):.4f} vs "
          f"{statistics.median([s['slack_cap'] for s in pos]):.4f}")
    print(f"- |nu| range {min(s['nu'] for s in S):.5f}-{max(s['nu'] for s in S):.5f}; gap = 0 with Delta e = 0 in "
          f"{sum(1 for s in z if s['dist'] == 0)} of {len(z)}")


if __name__ == "__main__":
    report() if sys.argv[1:] == ["report"] else run()
