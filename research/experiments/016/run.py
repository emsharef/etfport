"""Experiment 016 (D6): does the incumbent's position relative to the root target, or increasing differences
of the root value in (today's active holding, future ETF availability), decide the future-ETF channel's sign?
Registered design: experiments/016-m3-crossing.md.

Reuses, with attribution, red's reviewed machinery: `make`, `bayes`, `returns`, `funded_projection` from
checks/red-m3-definition/check.py, and `solve`, `bracket`, `ce`, `SOL` from experiments/008/red_reproduce.py.
Experiment 015's certified-bracket method and its Deviation-1 widening rule are kept.

Run:    uv run python experiments/016/run.py          (solves; writes experiments/016/results.json)
Report: uv run python experiments/016/run.py report   (reads results.json; prints every table)
"""
from __future__ import annotations

import importlib.util
import itertools
import json
import os
import sys
import time
from fractions import Fraction as F
from multiprocessing import Pool
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT / "checks" / "red-m3-definition"))
from check import bayes, funded_projection, make  # noqa: E402

_spec = importlib.util.spec_from_file_location("red008", ROOT / "experiments" / "008" / "red_reproduce.py")
red008 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(red008)

RHOS = [F(5) + F(k, 2) for k in range(11)]                      # 5, 5.5, ..., 10
COSTS_A = {"zero": (F(0),) * 4, "INST_A-like": (F(1, 2000), F(0), F(1, 2000), F(1, 2000))}
TILTS = {"tilt 31/50 (INST_A)": F(31, 50), "no factor-2 tilt": F(0)}
EXPO1 = F(23, 25) * F(43, 100) + F(1767, 10000)                   # INST_A's factor-1 exposure, 0.5723
A0_A = sorted({F(k, 20) for k in range(13)} | {F(43, 100)})       # 0, 0.05, ..., 0.60 and 0.43
COSTS_12 = {"zero": (F(0),) * 4, "all four 1/100": (F(1, 100),) * 4}
A0_12 = [F(k, 20) for k in range(11)]                             # 0, 0.05, ..., 0.50; ETF 1/2 - a0
CELLS = [("F", "N"), ("E", "N"), ("F", "E"), ("E", "E")]
TOL = 1e-7                                                        # "zero" for optimizer outputs


def inst_A(a0, cost, tilt, rho):
    """INST_A with one ETF (1, 0); incumbent active a0, ETF chosen so factor-1 exposure stays 0.5723."""
    ab, as_, eb, es = COSTS_A[cost]
    e0 = EXPO1 - F(23, 25) * a0
    return make(BA=(F(23, 25), TILTS[tilt]), BE=((F(1), F(0)),), cE=(F(3, 10000),),
                lam1=(F(1, 100), F(1, 25)), lam2=F(1, 100), alphas=(F(-1, 100), F(1, 50)),
                sizes=(F(9, 100), F(2, 25), F(3, 200), F(1, 100)),
                kb=(ab, eb), ks=(as_, es), x0=(a0, e0), rho=rho)


def inst_12(a0, cost, rho, own=False):
    """Claim 012's family (B^A=(1,0), B^E=(0,1), c^E=0, theta_+-=(+-1/2, -+1/2, 0) equally likely, all
    shocks zero), with incumbent (a0, 1/2 - a0, cash 1/2); own=True gives the claim's all-cash incumbent."""
    k = COSTS_12[cost]
    x0 = (F(0), F(0)) if own else (a0, F(1, 2) - a0)
    Theta = [(F(1, 2), F(-1, 2), F(0)), (F(-1, 2), F(1, 2), F(0))]
    return dict(BA=(F(1), F(0)), BE=((F(0), F(1)),), cE=(F(0),), Theta=Theta,
                pi0={t: F(1, 2) for t in Theta}, shocks=[(F(1), (F(0), F(0)), F(0), (F(0),))],
                kb=(k[0], k[2]), ks=(k[1], k[3]), x0=x0, h0=1 - sum(x0), rho=rho)


def specs():
    out = []
    for cost, tilt, rho, a0 in itertools.product(COSTS_A, TILTS, RHOS, A0_A):
        out.append(dict(family="INST_A", cost=cost, tilt=tilt, rho=str(rho), a0=str(a0)))
    for cost, rho, a0 in itertools.product(COSTS_12, RHOS, A0_12):
        out.append(dict(family="claim 012", cost=cost, tilt="-", rho=str(rho), a0=str(a0)))
    for cost, rho in itertools.product(COSTS_12, RHOS + [F(20)]):
        out.append(dict(family="claim 012 own incumbent", cost=cost, tilt="-", rho=str(rho), a0="0"))
    return out


def build(s):
    rho, a0 = F(s["rho"]), F(s["a0"])
    if s["family"] == "INST_A":
        return inst_A(a0, s["cost"], s["tilt"], rho)
    return inst_12(a0, s["cost"], rho, own=s["family"] == "claim 012 own incumbent")


def reduced(I, a):
    """Instance whose E root equals the original root with today's active holding forced to a.
    The active trade a - a0 is paid from cash, and any shortfall by the least ETF sale that funds it;
    after a forced sale cash is zero, so a buy-back would need a further ETF sale (a dominated round trip)."""
    a0, e0 = I["x0"]; h0 = I["h0"]
    kbA, kbE = I["kb"]; ksA, ksE = I["ks"]
    if a >= a0:
        need = (a - a0) * (1 + kbA)
        if need <= h0:
            h, e = h0 - need, e0
        else:
            q = (need - h0) / (1 - ksE)
            assert q <= e0, "a beyond a_max"
            h, e = F(0), e0 - q
    else:
        h, e = h0 + (a0 - a) * (1 - ksA), e0
    J = dict(I); J["x0"], J["h0"] = (a, e), h
    return J


def a_max(I):
    a0, e0 = I["x0"]
    return a0 + (I["h0"] + e0 * (1 - I["ks"][1])) / (1 + I["kb"][0])


def cell(I, B, D, R):
    """Solve cell (D, R), bracket it, and record the root trade and binding constraints."""
    V, u0 = red008.solve(I, B, D, R)
    if V is None:   # experiment 015's fallback
        V, u0 = red008.solve(I, B, D, R, solver="SCS", eps_abs=1e-10, eps_rel=1e-10, max_iters=200000)
    if V is None:
        return None
    U1 = red008.SOL[0]
    try:   # Deviation 2: a bracket that cannot be formed is recorded as missing (unresolved by rule)
        b = red008.bracket(I, B, D, R, u0, U1)
    except (ValueError, AssertionError) as err:
        print(f"bracket failed: {I['x0']} {I['h0']} rho {I['rho']} cell {D}{R}: {err}", flush=True)
        b = None
    x0 = np.array([float(x) for x in I["x0"]]); h0 = float(I["h0"])
    kb = np.array([float(x) for x in I["kb"]]); ks = np.array([float(x) for x in I["ks"]])
    u = np.array(u0, float)
    if D == "E":
        u[0] = 0.0
    x1, h1, u = funded_projection(x0, h0, u, kb, ks)
    Y, P0, _ = B
    nodecash0 = nodeetf0 = 0.0
    if R != "N":
        for y in Y:
            if P0[y] == 0:
                continue
            g = np.array([1 + float(r) for r in y[1]])
            v = np.array(U1[y], float)
            if R == "E":
                v[0] = 0.0
            xn, hn, _ = funded_projection(g * x1, h1, v, kb, ks)
            nodecash0 += float(P0[y]) * (hn <= TOL)
            nodeetf0 += float(P0[y]) * (xn[1] <= TOL)
    d = lambda z: "buy" if z > TOL else "sell" if z < -TOL else "none"  # noqa: E731
    return dict(bracket=None if b is None else [float(b[0]), float(b[1])],
                point=float(red008.ce(V, I["rho"])), u0=[float(z) for z in u],
                dirA=d(u[0]), dirE=d(u[1]), cash=float(h1), active=float(x1[0]), etf=float(x1[1]),
                adjustable=float(h1 + x1[1]),
                binding=dict(root_cash_zero=bool(h1 <= TOL), root_etf_zero=bool(x1[1] <= TOL),
                             root_active_zero=bool(x1[0] <= TOL),
                             prob_node_cash_zero=nodecash0, prob_node_etf_zero=nodeetf0))


def task(s):
    t0 = time.time()
    I = build(s)
    B = bayes(I)
    row = dict(s)
    row["cells"] = {D + R: cell(I, B, D, R) for D, R in CELLS}
    am = a_max(I)
    grid = sorted({F(k, 20) for k in range(21) if F(k, 20) < am} | {I["x0"][0], am})
    pts = []
    for a in grid:
        J = reduced(I, a)
        BJ = B   # beliefs do not depend on holdings
        cE, cN = cell(J, BJ, "E", "E"), cell(J, BJ, "E", "N")
        pts.append(dict(a=float(a), a_exact=str(a),
                        WE=None if cE is None else cE["bracket"], WN=None if cN is None else cN["bracket"],
                        WE_point=None if cE is None else cE["point"], WN_point=None if cN is None else cN["point"],
                        adjE=None if cE is None else cE["adjustable"], adjN=None if cN is None else cN["adjustable"]))
    row["grid"] = pts
    row["a_max"] = float(am)
    row["seconds"] = time.time() - t0
    return row


def run():
    t0 = time.time()
    S = specs()
    rows = []
    with Pool(int(os.environ.get("PROCS", "8"))) as pool:
        for k, row in enumerate(pool.imap(task, S, chunksize=1)):
            rows.append(row)
            if k % 50 == 0:
                print(f"{k + 1}/{len(S)} done, {time.time() - t0:.0f} s", flush=True)
    (HERE / "results.json").write_text(json.dumps(rows, indent=0))
    print(f"{len(rows)} instances, seconds: {time.time() - t0:.0f}")


# ---------------------------------------------------------------- analysis (registered rules)

def sign(iv):
    return "?" if iv is None else "+" if iv[0] > 0 else "-" if iv[1] < 0 else "?"


def report():
    rows = json.load(open(HERE / "results.json"))
    brs = [c["bracket"] for r in rows for c in r["cells"].values() if c and c["bracket"]]
    brs += [p[k] for r in rows for p in r["grid"] for k in ("WE", "WN") if p[k]]
    inv = max(max(0.0, b[0] - b[1]) for b in brs)
    tau = 10 * inv
    print(f"largest bracket inversion {inv:.2e} bp; tau = {tau:.2e} bp; brackets {len(brs)}")
    wid = lambda b: None if b is None else (min(b) - tau, max(b) + tau)  # noqa: E731

    def add(plus, minus):
        if any(b is None for b in plus + minus):
            return None
        return (sum(b[0] for b in plus) - sum(b[1] for b in minus), sum(b[1] for b in plus) - sum(b[0] for b in minus))

    missing = 0
    out = []
    for r in rows:
        c = r["cells"]
        cb = {k: wid(v["bracket"]) if v else None for k, v in c.items()}
        chan = add([cb["FE"], cb["EN"]], [cb["EE"], cb["FN"]])
        dN = add([cb["FN"]], [cb["EN"]]); dE = add([cb["FE"]], [cb["EE"]])
        G = [add([wid(p["WE"])], [wid(p["WN"])]) for p in r["grid"]]
        missing += sum(g is None for g in G) + (chan is None)
        steps = [add([G[k + 1]], [G[k]]) if G[k] and G[k + 1] else None for k in range(len(G) - 1)]
        ss = [sign(d) for d in steps]
        # Milgrom-Shannon single crossing, both orientations, on every grid pair a < a'
        scp_up = scp_down = 0
        for i, j in itertools.combinations(range(len(G)), 2):
            wN = add([wid(r["grid"][j]["WN"])], [wid(r["grid"][i]["WN"])])
            wE = add([wid(r["grid"][j]["WE"])], [wid(r["grid"][i]["WE"])])
            sN, sE = sign(wN), sign(wE)
            scp_up += (sN == "+" and sE == "-")
            scp_down += (sN == "-" and sE == "+")

        def direction(ks):
            p, n = sum(ss[k] == "+" for k in ks), sum(ss[k] == "-" for k in ks)
            u = len(ks) - p - n
            d = "increasing" if p and not n else "decreasing" if n and not p else "not monotone" if p and n else "unresolved"
            return d, u

        gdir, gun = direction(range(len(steps)))
        a0 = float(F(r["a0"])) if r["family"] != "claim 012 own incumbent" else 0.0
        aE = a0 + (c["FE"]["u0"][0] if c["FE"] else 0.0)
        aN = a0 + (c["FN"]["u0"][0] if c["FN"] else 0.0)
        xs = [p["a"] for p in r["grid"]]
        lo_a, hi_a = min(a0, aE, aN), max(a0, aE, aN)
        i0 = max([k for k, x in enumerate(xs) if x <= lo_a + 1e-12] or [0])
        i1 = min([k for k, x in enumerate(xs) if x >= hi_a - 1e-12] or [len(xs) - 1])
        if i1 <= i0:
            i1 = min(i0 + 1, len(xs) - 1)
        ldir, lun = direction(range(i0, i1))
        dA = [c[k]["dirA"] if c[k] else "?" for k in ("FE", "FN")]
        tdir = dA[0] if dA[0] == dA[1] else "split"
        sg = {"increasing": 1, "decreasing": -1}

        def predict(gd):
            if gd not in sg or tdir in ("split", "?"):
                return None
            return {"buy": 1, "sell": -1, "none": 0}[tdir] * sg[gd]

        cs = sign(chan)

        def verdict(p):
            if p is None:
                return "no prediction"
            if p == 0:
                return "match (zero)" if cs == "?" else "mismatch"
            if cs == "?":
                return "unresolved"
            return "match" if (cs == "+") == (p > 0) else "mismatch"

        adjAE = c["FE"]["adjustable"] if c["FE"] else None
        adjBN = c["EN"]["adjustable"] if c["EN"] else None
        wpred = None if adjAE is None or adjBN is None or abs(adjAE - adjBN) <= 1e-6 else (1 if adjAE > adjBN else -1)
        out.append(dict(r=r, chan=chan, cs=cs, dN=dN, dE=dE, tdir=tdir, gdir=gdir, gun=gun, ldir=ldir, lun=lun,
                        pg=verdict(predict(gdir)), pl=verdict(predict(ldir)), pw=verdict(wpred),
                        scp_up=scp_up, scp_down=scp_down, steps=ss, aE=aE, aN=aN, adjAE=adjAE, adjBN=adjBN,
                        G=G, xs=xs))
    print(f"missing brackets (unresolved by rule): {missing}\n")

    fams = ["INST_A", "claim 012", "claim 012 own incumbent"]
    # 1. sign maps: channel sign by incumbent (rows) and rho (columns); letters give today's trade direction
    print("## Sign maps (channel sign; b/s/n/x = root active trade under F,E and F,N: buy/sell/none/split)\n")
    for fam in fams:
        keys = sorted({(o["r"]["cost"], o["r"]["tilt"]) for o in out if o["r"]["family"] == fam})
        for cost, tilt in keys:
            rs = [o for o in out if o["r"]["family"] == fam and o["r"]["cost"] == cost and o["r"]["tilt"] == tilt]
            rhos = sorted({F(o["r"]["rho"]) for o in rs}); a0s = sorted({F(o["r"]["a0"]) for o in rs})
            print(f"**{fam}, costs {cost}, {tilt}**\n")
            print("| a0 \\ rho | " + " | ".join(str(float(x)) for x in rhos) + " |")
            print("|---" * (len(rhos) + 1) + "|")
            for a0 in a0s:
                cellv = []
                for rho in rhos:
                    o = next(o for o in rs if F(o["r"]["rho"]) == rho and F(o["r"]["a0"]) == a0)
                    cellv.append(o["cs"] + {"buy": "b", "sell": "s", "none": "n"}.get(o["tdir"], "x"))
                print(f"| {float(a0):.3f} | " + " | ".join(cellv) + " |")
            print()
    # 2. switch points along rho
    print("## Switch points in rho (adjacent grid values with certified opposite channel signs)\n")
    for fam in fams:
        for key in sorted({(o["r"]["cost"], o["r"]["tilt"], o["r"]["a0"]) for o in out if o["r"]["family"] == fam},
                          key=lambda k: (k[0], k[1], F(k[2]))):
            rs = sorted([o for o in out if (o["r"]["family"], o["r"]["cost"], o["r"]["tilt"], o["r"]["a0"]) == (fam,) + key],
                        key=lambda o: F(o["r"]["rho"]))
            sw = [f"{rs[k]['r']['rho']}->{rs[k + 1]['r']['rho']} ({rs[k]['cs']}{rs[k + 1]['cs']})"
                  for k in range(len(rs) - 1) if {rs[k]["cs"], rs[k + 1]["cs"]} == {"+", "-"}]
            unres = [o["r"]["rho"] for o in rs if o["cs"] == "?"]
            td = [o["r"]["rho"] for k, o in enumerate(rs[1:]) if o["tdir"] != rs[k]["tdir"]]
            print(f"- {fam} | {key[0]} | {key[1]} | a0 {float(F(key[2])):.3f}: switches {sw or 'none'}; "
                  f"unresolved at rho {unres or 'none'}; trade direction changes entering rho {td or 'none'}")
    print()
    # 3. counts
    print("## Channel sign by today's trade direction, and prediction verdicts\n")
    for fam in fams:
        rs = [o for o in out if o["r"]["family"] == fam]
        print(f"**{fam}** ({len(rs)} instances)")
        for td in ("buy", "sell", "none", "split"):
            t = [o for o in rs if o["tdir"] == td]
            if t:
                print(f"- trade {td}: channel + {sum(o['cs'] == '+' for o in t)}, - {sum(o['cs'] == '-' for o in t)}, "
                      f"unresolved {sum(o['cs'] == '?' for o in t)}")
        for g in ("increasing", "decreasing", "not monotone", "unresolved"):
            t = [o for o in rs if o["gdir"] == g]
            if t:
                print(f"- G over the whole grid {g}: {len(t)} (steps unresolved: max {max(o['gun'] for o in t)})")
        for g in ("increasing", "decreasing", "not monotone", "unresolved"):
            t = [o for o in rs if o["ldir"] == g]
            if t:
                print(f"- G over the local range {g}: {len(t)}")
        for lab, k in (("whole-grid increasing differences", "pg"), ("local increasing differences", "pl"),
                       ("adjustable wealth A_E vs B_N", "pw")):
            v = {}
            for o in rs:
                v[o[k]] = v.get(o[k], 0) + 1
            print(f"- prediction from {lab}: {v}")
        print(f"- single-crossing violations (certified pairs): upward {sum(o['scp_up'] for o in rs)}, "
              f"downward {sum(o['scp_down'] for o in rs)}; instances with any upward {sum(o['scp_up'] > 0 for o in rs)}, "
              f"any downward {sum(o['scp_down'] > 0 for o in rs)}")
        print()
    # 4. every mismatch and every no-prediction case, individually
    print("## Every mismatch (any of the three predictions), with binding constraints and cost directions\n")
    n = 0
    for o in out:
        if "mismatch" not in (o["pg"], o["pl"], o["pw"]):
            continue
        n += 1
        r = o["r"]; c = r["cells"]
        b = lambda k: (f"{k}: dir A/E {c[k]['dirA']}/{c[k]['dirE']}, cash {c[k]['cash']:.4f}, ETF {c[k]['etf']:.4f}, "  # noqa: E731
                       f"node cash 0 w.p. {c[k]['binding']['prob_node_cash_zero']:.2f}, node ETF 0 w.p. "
                       f"{c[k]['binding']['prob_node_etf_zero']:.2f}") if c[k] else f"{k}: missing"
        print(f"- {r['family']} | {r['cost']} | {r['tilt']} | rho {r['rho']} | a0 {float(F(r['a0'])):.3f}: channel "
              f"[{o['chan'][0]:+.4f}, {o['chan'][1]:+.4f}] bp; trade {o['tdir']}; G whole {o['gdir']} -> {o['pg']}; "
              f"local {o['ldir']} -> {o['pl']}; adjustable A_E {o['adjAE']:.4f} vs B_N {o['adjBN']:.4f} -> {o['pw']}; "
              f"steps {''.join(o['steps'])}")
        for k in ("FE", "FN", "EE", "EN"):
            print(f"  - {b(k)}")
    print(f"\nmismatches: {n}\n")
    print("## No-prediction and not-monotone instances\n")
    for o in out:
        if o["pg"] == "no prediction" or o["gdir"] == "not monotone":
            r = o["r"]
            print(f"- {r['family']} | {r['cost']} | {r['tilt']} | rho {r['rho']} | a0 {float(F(r['a0'])):.3f}: channel {o['cs']}; "
                  f"trade {o['tdir']}; G whole {o['gdir']}; local {o['ldir']} -> {o['pl']}; steps {''.join(o['steps'])}")
    # 5. consistency checks
    dev = max(abs(p["WE_point"] - o["r"]["cells"]["EE"]["point"]) + abs(p["WN_point"] - o["r"]["cells"]["EN"]["point"])
              for o in out for p in o["r"]["grid"]
              if o["r"]["cells"]["EE"] and o["r"]["cells"]["EN"] and p["WE_point"] and p["WN_point"]
              and F(p["a_exact"]) == F(o["r"]["a0"]))
    print(f"\nconsistency: largest |W_R(a0) - CE_(E,R)| (points, E and N summed) = {dev:.2e} bp")
    sand = 0
    for o in out:   # the reduced-problem sandwich G(a*_N) - G(a0) <= channel <= G(a*_E) - G(a0), grid argmaxes
        r = o["r"]; xs = o["xs"]
        pE = [p["WE_point"] for p in r["grid"]]; pN = [p["WN_point"] for p in r["grid"]]
        if None in pE or None in pN or o["chan"] is None:
            continue
        a0 = 0.0 if r["family"] == "claim 012 own incumbent" else float(F(r["a0"]))
        k0 = min(range(len(xs)), key=lambda k: abs(xs[k] - a0))
        kE, kN = int(np.argmax(pE)), int(np.argmax(pN))
        g = [e - m for e, m in zip(pE, pN)]
        sand += not (g[kN] - g[k0] - 1e-3 <= o["chan"][1] and o["chan"][0] <= g[kE] - g[k0] + 1e-3)
    print(f"diagnostic: instances where the grid-argmax sandwich misses the channel interval by > 1e-3 bp: {sand} "
          f"(grid argmaxes approximate the root optima; not a certificate)")
    tot = sum(r["seconds"] for r in rows)
    print(f"total solve seconds (summed over processes): {tot:.0f}")


if __name__ == "__main__":
    report() if sys.argv[1:] == ["report"] else run()
