"""Experiment 017 (D6): calibrated magnitude and prevalence of the continuation channels and region crossings,
the loss from a cost-aware myopic root, and the per-dollar premium of future ETF adjustment.
Registered design: experiments/017-m3-calibrated-magnitude.md.

Reuses, with attribution: experiment 016's `cell` (red's `solve` and `bracket` from experiments/008/red_reproduce.py,
with 016's binding-constraint bookkeeping); red's `make`, `bayes`, `returns` (checks/red-m3-definition/check.py);
math's `solve_fixed` and `beta` (checks/exp015-premia/check.py); the exact M2 solver (experiments/004/m2.py).

Run:    uv run python -W ignore experiments/017/run.py          (stage 1; writes experiments/017/results.json)
        uv run python -W ignore experiments/017/run.py crossing (stage 2; writes experiments/017/crossing.json)
Report: uv run python experiments/017/run.py report
        uv run python experiments/017/run.py exp016             (part 3 on experiment 016's committed outputs)
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
from fractions import Fraction as F
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


r16 = _load("r16", ROOT / "experiments" / "016" / "run.py")
math015 = _load("math015", ROOT / "checks" / "exp015-premia" / "check.py")
sys.path.insert(0, str(ROOT / "experiments" / "004"))
import m2  # noqa: E402

make, bayes, returns, red008 = r16.make, r16.bayes, math015.returns, r16.red008

# ---- calibration (data: French 3-factor file, July 2025 cut, 1963Q3-2025Q2, 248 quarters, per quarter, gross)
MKT_MEAN, MKT_SD = F(184, 10000), F(854, 10000)
HML_MEAN, HML_SD = F(897, 100000), F(6095, 100000)
# premia are known at their sample means; learning is about alpha only (assumed)
# ---- assumed
BA = (F(1), F(3, 10))                                   # active: market 1, HML tilt 0.3 (as experiment 006)
BE = ((F(1), F(0)),)                                    # one market ETF
CE = (F(1, 10000),)                                     # ETF drag 1 bp per quarter (as 006)
S_ETF = F(2, 1000)                                      # ETF residual +-0.2% (as 006)
ALPHA_MEAN = {"-25 bp": F(-25, 10000), "0": F(0), "+25 bp": F(25, 10000)}
ALPHA_HALF = F(50, 10000)                               # alpha in {m - 50 bp, m + 50 bp}, equally likely
# active residual: 5-point binomial lattice with step 1% = the alpha gap, SD 1% (006's lower residual size),
# so adjacent alpha values share observations and one quarter only partly reveals alpha
ZA = [(F(k, 16), F(j - 2, 100)) for j, k in enumerate((1, 4, 6, 4, 1))]
S_ACT = F(1, 100)
RHOS = [F(2), F(5), F(10)]
A0 = [F(0), F(15, 100), F(30, 100), F(45, 100), F(60, 100)]
MKT_EXPO = F(60, 100)                                   # a0 + e0 = 0.6 (market exposure fixed), cash 0.4
COSTS = {  # (active buy, active sell, ETF buy, ETF sell); active rates from experiment 003's EDGAR medians
    "no-load": (F(0), F(0), F(1, 10000), F(1, 10000)),
    "front load 525 bp": (F(525, 9475), F(0), F(1, 10000), F(1, 10000)),   # L/(1-L), L = 525 bp -> 554 bp
    "deferred charge 100 bp": (F(0), F(1, 100), F(1, 10000), F(1, 10000)),
}
CELLS6 = [(D, R) for D in "FE" for R in "FEN"]


def instance(cost, rho, am, a0):
    """M3 instance in red's dict format (as `make` builds it), with a lattice active residual."""
    ab, as_, eb, es = COSTS[cost]
    Theta = [(MKT_MEAN, HML_MEAN, ALPHA_MEAN[am] + sgn * ALPHA_HALF) for sgn in (-1, 1)]
    shocks = [(F(1, 8) * pa, (s1 * MKT_SD, s2 * HML_SD), za, (se * S_ETF,))
              for s1, s2, se in itertools.product((-1, 1), repeat=3) for pa, za in ZA]
    x0 = (a0, MKT_EXPO - a0)
    return dict(BA=BA, BE=BE, cE=CE, Theta=Theta, pi0={t: F(1, 2) for t in Theta}, shocks=shocks,
                kb=(ab, eb), ks=(as_, es), x0=x0, h0=1 - sum(x0), rho=rho)


def specs():
    return [dict(cost=c, rho=str(r), alpha=a, a0=str(x)) for c, r, a, x in itertools.product(COSTS, RHOS, ALPHA_MEAN, A0)]


def build(s):
    return instance(s["cost"], F(s["rho"]), s["alpha"], F(s["a0"]))


def myopic(I):
    """Cost-aware myopic root: M2's one-quarter optimum (exact), with the belief mean and the shock covariance."""
    th = I["Theta"]
    lam = (sum(t[0] for t in th) / len(th), sum(t[1] for t in th) / len(th))
    alpha = sum(t[2] for t in th) / len(th)
    J = m2.Instance2(BA=I["BA"], BE=I["BE"], sf=(MKT_SD, HML_SD), sA=S_ACT, sE=(S_ETF,), lam=lam, alpha=alpha,
                     cE=I["cE"], gamma=I["rho"], kbuy=I["kb"], ksell=I["ks"], w0=I["x0"], k0=I["h0"], wbar=(F(1), F(1)))
    assert not m2.check_instance(J), m2.check_instance(J)
    _, w, _ = m2.solve(J, "F", exact=True)
    u = [w[i] - I["x0"][i] for i in range(2)]
    fee = sum(I["kb"][i] * u[i] if u[i] > 0 else -I["ks"][i] * u[i] for i in range(2))
    K = dict(I)
    K["x0"], K["h0"] = tuple(w), I["h0"] - sum(u) - fee
    assert K["h0"] >= 0
    return K, [float(x) for x in u]


def checks(I):
    Y, P0, post = bayes(I)
    pos = all(1 + r > 0 for t in I["Theta"] for s in I["shocks"] for r in returns(I, t, s)[1])
    amb = [y for y in Y if P0[y] > 0 and sum(v > 0 for v in post[y].values()) > 1]
    return dict(positive=pos, observations=sum(P0[y] > 0 for y in Y), ambiguous=len(amb),
                prob_ambiguous=float(sum(P0[y] for y in amb)))


def hedge(I, B, u0):
    """Registered exploratory measure: sum_y P0(y) |Corr_{post(y)}(g_E^2, W^N_y)|, W^N_y the no-trade node wealth
    after root trade u0 (claim 023's definition), g_E^2 the ETF's second-quarter gross return."""
    Y, P0, post = B
    x0 = np.array([float(x) for x in I["x0"]]); h0 = float(I["h0"])
    kb = np.array([float(x) for x in I["kb"]]); ks = np.array([float(x) for x in I["ks"]])
    u = np.array(u0, float)
    h = h0 - u.sum() - kb @ np.maximum(u, 0) - ks @ np.maximum(-u, 0)
    x = np.maximum(x0 + u, 0)
    tot = 0.0
    for y in Y:
        if P0[y] == 0:
            continue
        m = x * np.array([1 + float(r) for r in y[1]])
        ws, gs, ps = [], [], []
        for t, pt in post[y].items():
            if pt > 0:
                for s in I["shocks"]:
                    g = np.array([1 + float(r) for r in returns(I, t, s)[1]])
                    ws.append(h + m @ g); gs.append(g[1]); ps.append(float(pt * s[0]))
        ws, gs, ps = np.array(ws), np.array(gs), np.array(ps)
        mw, mg = ps @ ws, ps @ gs
        cov = ps @ ((ws - mw) * (gs - mg)); vw = ps @ (ws - mw) ** 2; vg = ps @ (gs - mg) ** 2
        tot += float(P0[y]) * (abs(cov) / math.sqrt(vw * vg) if vw > 0 and vg > 0 else 0.0)
    return tot


def task(s):
    t0 = time.time()
    I = build(s)
    B = bayes(I)
    row = dict(s, checks=checks(I))
    row["cells"] = {D + R: r16.cell(I, B, D, R) for D, R in CELLS6}
    K, uM = myopic(I)
    row["myopic_u0"] = uM
    row["myopic"] = r16.cell(K, B, "N", "F")
    prem = {}
    for name, c in (("A_N", "FN"), ("A_E", "FE"), ("B_N", "EN"), ("B_E", "EE")):
        if row["cells"][c] is None:
            continue
        u0 = row["cells"][c]["u0"]
        cE, h = math015.solve_fixed(I, B, u0, "E")
        cN, _ = math015.solve_fixed(I, B, u0, "N")
        adj = row["cells"][c]["adjustable"]
        prem[name] = dict(phi=(cE - cN) * 1e4, beta=math015.beta(I, u0, h) * 1e4, adjustable=adj,
                          per_dollar=(cE - cN) * 1e4 / adj if adj > 1e-9 else None, hedge=hedge(I, B, u0))
    row["premia"] = prem
    row["seconds"] = time.time() - t0
    return row


def run():
    t0 = time.time()
    S = specs()
    rows = []
    with Pool(int(os.environ.get("PROCS", "8"))) as pool:
        for k, row in enumerate(pool.imap(task, S, chunksize=1)):
            rows.append(row)
            if k % 20 == 0:
                print(f"{k + 1}/{len(S)} done, {time.time() - t0:.0f} s", flush=True)
    (HERE / "results.json").write_text(json.dumps(rows, indent=0))
    print(f"{len(rows)} instances, seconds: {time.time() - t0:.0f}")


# ---------------------------------------------------------------- stage 2: region crossings

def edges(rs, R):
    tg = lambda r, d: [float(F(r["a0"])) + r["cells"]["F" + R]["u0"][0]] if r["cells"]["F" + R] and r["cells"]["F" + R]["dirA"] == d else []  # noqa: E731
    buy = sum((tg(r, "buy") for r in rs), []); sell = sum((tg(r, "sell") for r in rs), [])
    return (statistics.median(buy) if buy else None, statistics.median(sell) if sell else None)


def crossing_points(rows):
    out, groups = [], {}
    for r in rows:
        if COSTS[r["cost"]][0] == 0 and COSTS[r["cost"]][1] == 0:
            continue   # no active rate: the no-active-trade band is a point
        groups.setdefault((r["cost"], r["rho"], r["alpha"]), []).append(r)
    for (cost, rho, am), rs in groups.items():
        LN, UN = edges(rs, "N"); LE, UE = edges(rs, "E")
        for x, y, side in ((LN, LE, "lower"), (UN, UE, "upper")):
            if x is None or y is None or abs(x - y) <= 1e-4:
                continue
            lo, hi = min(x, y), max(x, y)
            for k in range(1, 6):
                a0 = F(round((lo + (hi - lo) * k / 6) * 1e6), 10**6)
                if 0 <= a0 <= MKT_EXPO:
                    out.append(dict(cost=cost, rho=rho, alpha=am, a0=str(a0), side=side, gap=[lo, hi],
                                    edges=dict(LN=LN, UN=UN, LE=LE, UE=UE)))
    return out


def cross_task(s):
    I = build(s)
    B = bayes(I)
    cells = {D + R: r16.cell(I, B, D, R) for D, R in r16.CELLS}
    ub = {}
    for R in "NE":
        e = cells["E" + R]
        V, u0 = red008.solve(I, B, "E", R)
        U1 = red008.SOL[0]
        try:
            b = None if V is None else red008.bracket(I, B, "F", R, u0, U1)
        except (ValueError, AssertionError):
            b = None
        ub[R] = None if b is None or e is None or e["bracket"] is None else float(b[1]) - min(e["bracket"])
    return dict(s, cells=cells, ub=ub)


def crossing():
    rows = json.load(open(HERE / "results.json"))
    P = crossing_points(rows)
    print(f"{len(P)} fine incumbents", flush=True)
    with Pool(int(os.environ.get("PROCS", "8"))) as pool:
        res = pool.map(cross_task, P, chunksize=1)
    (HERE / "crossing.json").write_text(json.dumps(res, indent=0))


# ---------------------------------------------------------------- analysis (registered rules)

def tau_of(rows, extra=()):
    brs = [c["bracket"] for r in rows for c in list(r["cells"].values()) + [r.get("myopic")] if c and c["bracket"]]
    brs += [c["bracket"] for r in extra for c in r["cells"].values() if c and c["bracket"]]
    inv = max(max(0.0, b[0] - b[1]) for b in brs)
    return inv, 10 * inv, len(brs)


def report():
    rows = json.load(open(HERE / "results.json"))
    cr = json.load(open(HERE / "crossing.json")) if (HERE / "crossing.json").exists() else []
    inv, tau, nb = tau_of(rows, cr)
    print(f"largest bracket inversion {inv:.2e} bp; tau = {tau:.2e} bp; brackets {nb}")
    wid = lambda b: None if b is None else (min(b) - tau, max(b) + tau)  # noqa: E731

    def iv(r, plus, minus):
        bs = [wid(r["cells"][c]["bracket"]) if r["cells"][c] else None for c in plus + minus]
        if any(b is None for b in bs):
            return None
        p, m = bs[:len(plus)], bs[len(plus):]
        return (sum(b[0] for b in p) - sum(b[1] for b in m), sum(b[1] for b in p) - sum(b[0] for b in m))

    sg = lambda i: "?" if i is None else "+" if i[0] > 0 else "-" if i[1] < 0 else "?"  # noqa: E731
    fmt = lambda i: "missing" if i is None else f"[{i[0]:+.2f}, {i[1]:+.2f}]"  # noqa: E731
    print("\n## Fixture checks")
    print(f"positive returns in all: {all(r['checks']['positive'] for r in rows)}; ambiguous observations "
          f"{sorted({(r['checks']['ambiguous'], round(r['checks']['prob_ambiguous'], 3)) for r in rows})}")
    print("\n## Per instance (bp of initial wealth over the two quarters; per quarter = half)\n")
    print("| costs | rho | alpha mean | a0 | Delta_E - Delta_N | Delta_F - Delta_E | Delta_N | Delta_E | root active A_E / A_N | myopic u_A | myopic loss |")
    print("|---|---|---|---|---|---|---|---|---|---|---|")
    out = []
    for r in rows:
        e = iv(r, ["FE", "EN"], ["EE", "FN"]); a = iv(r, ["FF", "EE"], ["EF", "FE"])
        dN = iv(r, ["FN"], ["EN"]); dE = iv(r, ["FE"], ["EE"])
        ml = None
        if r["cells"]["FF"] and r["myopic"] and r["myopic"]["bracket"] and r["cells"]["FF"]["bracket"]:
            f, m = wid(r["cells"]["FF"]["bracket"]), wid(r["myopic"]["bracket"])
            ml = (max(f[0] - m[1], 0.0), f[1] - m[0])   # the loss is >= 0 by optimality
        o = dict(r=r, e=e, a=a, dN=dN, dE=dE, ml=ml)
        out.append(o)
        tr = lambda c: f"{r['cells'][c]['u0'][0]:+.3f}" if r["cells"][c] else "?"  # noqa: E731
        print(f"| {r['cost']} | {r['rho']} | {r['alpha']} | {float(F(r['a0'])):.2f} | {fmt(e)} | {fmt(a)} | {fmt(dN)} | {fmt(dE)} | "
              f"{tr('FE')} / {tr('FN')} | {r['myopic_u0'][0]:+.3f} | {fmt(ml)} |")
    print("\n## Shares and magnitudes\n")
    for lab, k in (("future-ETF channel", "e"), ("future-active channel", "a")):
        v = [o[k] for o in out]
        s = [sg(x) for x in v]
        mags = [max(abs(x[0]), abs(x[1])) if sg(x) != "?" else None for x in v]
        big = sum(1 for x in v if x is not None and (x[0] >= 2 or x[1] <= -2))
        print(f"- {lab}: + {s.count('+')}, - {s.count('-')}, unresolved {s.count('?')} of {len(v)}; "
              f"|certified| >= 2 bp over two quarters (1 bp/quarter): {big}; "
              f"median |point| {statistics.median([abs((x[0] + x[1]) / 2) for x in v if x]):.3f} bp; "
              f"max |point| {max(abs((x[0] + x[1]) / 2) for x in v if x):.3f} bp")
    ml = [o["ml"] for o in out if o["ml"]]
    print(f"- myopic loss: median midpoint {statistics.median([(x[0] + x[1]) / 2 for x in ml]):.3f} bp, "
          f"max {max((x[0] + x[1]) / 2 for x in ml):.3f} bp; certified >= 2 bp: {sum(x[0] >= 2 for x in ml)} of {len(ml)}; "
          f"certified > 0: {sum(x[0] > 0 for x in ml)}")
    for key in ("cost", "rho", "alpha", "a0"):
        print(f"\n**by {key}**")
        for v in sorted({o["r"][key] for o in out}, key=lambda z: (len(z), z)):
            os_ = [o for o in out if o["r"][key] == v]
            es = [sg(o["e"]) for o in os_]; as_ = [sg(o["a"]) for o in os_]
            mlv = [(o["ml"][0] + o["ml"][1]) / 2 for o in os_ if o["ml"]]
            emag = [abs((o["e"][0] + o["e"][1]) / 2) for o in os_ if o["e"]]
            print(f"- {v}: ETF channel +{es.count('+')} -{es.count('-')} ?{es.count('?')} (max |.| {max(emag):.2f} bp); "
                  f"active channel +{as_.count('+')} -{as_.count('-')} ?{as_.count('?')}; myopic loss max {max(mlv):.2f} bp")
    # region crossings
    print("\n## Region crossings (claim 022 part 3)\n")
    EPS = 1e-3
    groups = {}
    for r in cr:
        c = r["cells"]; cls = {}
        for R in "NE":
            f, e = c["F" + R], c["E" + R]
            if not (f and e and f["bracket"] and e["bracket"]):
                cls[R] = "?"
            elif wid(f["bracket"])[0] - wid(e["bracket"])[1] > 0:
                cls[R] = "+"
            elif r["ub"][R] is not None and r["ub"][R] <= EPS:
                cls[R] = "0"
            else:
                cls[R] = "?"
        kind = "E0<N" if (cls["E"], cls["N"]) == ("0", "+") else "N0<E" if (cls["N"], cls["E"]) == ("0", "+") else ""
        g = groups.setdefault((r["cost"], r["rho"], r["alpha"], r["side"]), dict(gap=r["gap"], pts=[]))
        g["pts"].append((float(F(r["a0"])), kind, cls))
    ncross = 0
    print("| costs | rho | alpha mean | edge | band-edge gap in a0 (width) | certified crossings of 5 | kind |")
    print("|---|---|---|---|---|---|---|")
    for (cost, rho, am, side), g in sorted(groups.items()):
        k = [p for p in g["pts"] if p[1]]
        ncross += bool(k)
        print(f"| {cost} | {rho} | {am} | {side} | [{g['gap'][0]:.4f}, {g['gap'][1]:.4f}] ({g['gap'][1] - g['gap'][0]:.4f}) | "
              f"{len(k)} | {', '.join(sorted({p[1] for p in k})) or '-'} |")
    ngr = len({(o['r']['cost'], o['r']['rho'], o['r']['alpha']) for o in out if o['r']['cost'] != 'no-load'})
    print(f"\ngroups (costs with an active rate x rho x alpha): {ngr}; edges searched {len(groups)}; "
          f"edges with a certified crossing {ncross}")
    inc = [o for o in out if o["dN"] and o["dE"] and ((sg(o["dN"]) == "+") != (sg(o["dE"]) == "+"))]
    print(f"stage-1 grid instances where exactly one of Delta_N, Delta_E is certified positive: {len(inc)}")
    # part 3: per-dollar premium on this grid
    print("\n## Per-dollar premium at the four optima (floating)\n")
    rule_adj = rule_phi = rule_pd = n = 0
    for o in out:
        p = o["r"]["premia"]; s = sg(o["e"])
        if s == "?" or len(p) < 4:
            continue
        n += 1
        d = p["A_E"]["adjustable"] - p["B_N"]["adjustable"]
        rule_adj += (s == ("+" if d > 0 else "-")) if abs(d) > 1e-6 else 0
        rule_phi += s == ("+" if p["A_E"]["phi"] > p["B_N"]["phi"] else "-")
        if p["A_E"]["per_dollar"] and p["B_N"]["per_dollar"]:
            rule_pd += s == ("+" if p["A_E"]["per_dollar"] > p["B_N"]["per_dollar"] else "-")
    print(f"resolved channels {n}: sign follows adjustable(A_E) - adjustable(B_N) in {rule_adj}; "
          f"phi(A_E) - phi(B_N) in {rule_phi}; per-dollar(A_E) - per-dollar(B_N) in {rule_pd}")
    print("\n| costs | rho | alpha | a0 | channel | adj A_E / B_N | phi A_E / B_N | per-dollar A_E / B_N | hedge A_E / B_N |")
    print("|---|---|---|---|---|---|---|---|---|")
    for o in out:
        p = o["r"]["premia"]
        if len(p) < 4:
            continue
        pdv = lambda k: f"{p[k]['per_dollar']:.2f}" if p[k]["per_dollar"] is not None else "-"  # noqa: E731
        print(f"| {o['r']['cost']} | {o['r']['rho']} | {o['r']['alpha']} | {float(F(o['r']['a0'])):.2f} | {sg(o['e'])} | "
              f"{p['A_E']['adjustable']:.3f} / {p['B_N']['adjustable']:.3f} | {p['A_E']['phi']:.2f} / {p['B_N']['phi']:.2f} | "
              f"{pdv('A_E')} / {pdv('B_N')} | {p['A_E']['hedge']:.3f} / {p['B_N']['hedge']:.3f} |")
    print(f"\ntotal solve seconds (summed over processes): {sum(r['seconds'] for r in rows):.0f}")


def exp016():
    """Part 3 on experiment 016's committed outputs: per-dollar premium and hedge at the 45 exceptions."""
    d = ROOT / "experiments" / "016"
    rows = json.load(open(d / "results.json")); pr = json.load(open(d / "premia.json"))
    brs = [c["bracket"] for r in rows for c in r["cells"].values() if c and c["bracket"]]
    brs += [p[k] for r in rows for p in r["grid"] for k in ("WE", "WN") if p[k]]
    tau = 10 * max(max(0.0, b[0] - b[1]) for b in brs)
    w = lambda b: (min(b) - tau, max(b) + tau)  # noqa: E731
    print("| family | costs | tilt | rho | a0 | channel | adj A_E / B_N | per-dollar A_E / B_N (bp per unit) | phi A_E - B_N | "
          "log adj ratio | log per-dollar ratio | hedge A_E / B_N | per-dollar explains | hedge orders per-dollar |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    n = expl = hord = 0
    for r, p in zip(rows, pr):
        c = r["cells"]
        if p is None or any(c[k] is None or c[k]["bracket"] is None for k in ("FE", "EN", "EE", "FN")):
            continue
        b = {k: w(c[k]["bracket"]) for k in ("FE", "EN", "EE", "FN")}
        lo = b["FE"][0] + b["EN"][0] - b["EE"][1] - b["FN"][1]; hi = b["FE"][1] + b["EN"][1] - b["EE"][0] - b["FN"][0]
        cs = "+" if lo > 0 else "-" if hi < 0 else "?"
        aE, aB = c["FE"]["adjustable"], c["EN"]["adjustable"]
        if cs == "?" or abs(aE - aB) <= 1e-6 or cs == ("+" if aE > aB else "-"):
            continue
        n += 1
        I = r16.build(r); B = bayes(I)
        hE, hB = hedge(I, B, c["FE"]["u0"]), hedge(I, B, c["EN"]["u0"])
        pE, pB = p["A_E"]["phi"] / aE, p["B_N"]["phi"] / aB
        dphi = p["A_E"]["phi"] - p["B_N"]["phi"]
        ex = cs == ("+" if dphi > 0 else "-")
        ho = (pE > pB) == (hE > hB)
        expl += ex; hord += ho
        print(f"| {r['family']} | {r['cost']} | {r['tilt']} | {r['rho']} | {float(F(r['a0'])):.2f} | {cs} | {aE:.3f} / {aB:.3f} | "
              f"{pE:.2f} / {pB:.2f} | {dphi:+.2f} | {math.log(aE / aB):+.3f} | {math.log(pE / pB):+.3f} | {hE:.3f} / {hB:.3f} | "
              f"{'yes' if ex else 'no'} | {'yes' if ho else 'no'} |")
    print(f"\nexceptions {n}; sign of phi(A_E) - phi(B_N) (adjustable x per-dollar) matches the channel in {expl}; "
          f"hedge orders the per-dollar premia in {hord}")


if __name__ == "__main__":
    cmd = sys.argv[1:] or ["run"]
    {"run": run, "crossing": crossing, "report": report, "exp016": exp016}[cmd[0]]()
