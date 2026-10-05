"""Red's reproduction of experiment 016, written from the registered Design without reading run.py,
premia.py or crossing.py.

Instances are built from the Design's description: INST_A with the incumbent moved at fixed factor-1
exposure, claim 012's family at fixed total risky exposure 1/2, and claim 012's own all-cash incumbent.
Each (D, R) cell is solved and bracketed with red's experiment 008 engine (CLARABEL, SCS fallback,
certified Frank-Wolfe bracket). The channel is an interval sum, and signs are called after widening by
tau = 10 x the largest inversion over red's own brackets. Trade directions and adjustable wealth
(cash plus ETF at the funded projection) are read at the optimizers.

Usage: uv run python -W ignore experiments/016/red_reproduce.py [stage1|grid|crossings|report]
"""
import json
import sys
from fractions import Fraction as F
from multiprocessing import Pool
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "008"))
sys.path.insert(0, str(HERE.parent.parent / "checks" / "red-m3-definition"))
import red_reproduce as R8  # noqa: E402  (red's experiment 008 engine)
from check import bayes, funded_projection, make  # noqa: E402

BP = F(1, 10000)
RHOS = [F(10 + k, 2) for k in range(11)]                      # 5, 5.5, ..., 10
CELLS = [("F", "N"), ("E", "N"), ("F", "E"), ("E", "E")]


def inst_a(a0, cost, tilt, rho):
    a0 = F(a0)
    e0 = F(5723, 10000) - F(23, 25) * a0
    kb, ks = ((0, 0), (0, 0)) if cost == "zero" else ((5 * BP, 5 * BP), (0, 5 * BP))
    return make(BA=(F(23, 25), F(tilt)), BE=((F(1), F(0)),), cE=(F(3, 10000),),
                lam1=(F(1, 100), F(1, 25)), lam2=F(1, 100), alphas=(F(-1, 100), F(1, 50)),
                sizes=(F(9, 100), F(2, 25), F(3, 200), F(1, 100)),
                kb=tuple(F(x) for x in kb), ks=tuple(F(x) for x in ks), x0=(a0, e0), rho=F(rho))


def inst_012(a0, cost, rho, own=False):
    """Claim 012: B^A=(1,0), B^E=(0,1), c^E=0, theta = +-(1/2,-1/2,0) equally likely, shocks zero."""
    th = [(F(1, 2), F(-1, 2), F(0)), (F(-1, 2), F(1, 2), F(0))]
    k = F(0) if cost == "zero" else F(1, 100)
    x0 = (F(0), F(0)) if own else (F(a0), F(1, 2) - F(a0))
    return dict(BA=(F(1), F(0)), BE=((F(0), F(1)),), cE=(F(0),), Theta=th, pi0={t: F(1, 2) for t in th},
                shocks=[(F(1), (F(0), F(0)), F(0), (F(0),))], kb=(k, k), ks=(k, k), x0=x0,
                h0=1 - sum(x0), rho=F(rho))


def instances():
    out = []
    for cost in ("zero", "INST_A-like"):
        for tilt in (F(31, 50), F(0)):
            for a0 in sorted(set([F(k, 20) for k in range(13)] + [F(43, 100)])):
                for rho in RHOS:
                    out.append(dict(fam="INST_A", cost=cost, tilt=str(tilt), a0=str(a0), rho=str(rho)))
    for cost in ("zero", "1/100"):
        for a0 in [F(k, 20) for k in range(11)]:
            for rho in RHOS:
                out.append(dict(fam="012", cost=cost, tilt="-", a0=str(a0), rho=str(rho)))
        for rho in RHOS + [F(20)]:
            out.append(dict(fam="012 own", cost=cost, tilt="-", a0="0", rho=str(rho)))
    return out


def build(k):
    if k["fam"] == "INST_A":
        return inst_a(F(k["a0"]), k["cost"], F(k["tilt"]), F(k["rho"]))
    return inst_012(F(k["a0"]), k["cost"], F(k["rho"]), own=k["fam"] == "012 own")


def cell(I, B, D, R):
    V, u0 = R8.solve(I, B, D, R)
    if V is None:
        V, u0 = R8.solve(I, B, D, R, solver="SCS", eps_abs=1e-10, eps_rel=1e-10, max_iters=200000)
    if V is None:
        return None
    try:
        b = R8.bracket(I, B, D, R, u0, R8.SOL[0])
    except Exception as e:            # a failed bracket is recorded as missing
        print("bracket failed", D, R, e, flush=True)
        b = None
    kb = np.array([float(x) for x in I["kb"]]); ks = np.array([float(x) for x in I["ks"]])
    x0 = np.array([float(x) for x in I["x0"]])
    x, h, _ = funded_projection(x0, float(I["h0"]), np.asarray(u0, float), kb, ks)
    return dict(lo=None if b is None else min(b[0], b[1]), hi=None if b is None else max(b[0], b[1]),
                inv=None if b is None else max(0.0, b[0] - b[1]), pt=R8.ce(V, I["rho"]),
                uA=float(u0[0]), uE=float(u0[1]), cash=float(h), etf=float(x[1]), act=float(x[0]),
                adj=float(h + x[1]))


def stage1(k):
    I = build(k); B = bayes(I)
    return dict(k, cells={f"{D}{R}": cell(I, B, D, R) for D, R in CELLS})


def run_stage1():
    ks = instances()
    res = []
    with Pool(8) as p:
        for i, r in enumerate(p.imap(stage1, ks, chunksize=2)):
            res.append(r)
            if i % 50 == 0:
                print(f"stage1 {i}/{len(ks)}", flush=True)
    json.dump(res, open(HERE / "red_stage1.json", "w"))


def reduced(I, a):
    """Instance with the root active holding forced to a: the active trade a - a0 is paid from cash at
    its directional rate; any shortfall is covered by the least ETF sale, leaving cash zero."""
    a0, e0 = I["x0"]; h0 = I["h0"]
    kbA, kbE = I["kb"]; ksA, ksE = I["ks"]
    t = a - a0
    h = h0 - (t * (1 + kbA) if t > 0 else t * (1 - ksA))
    e = e0
    if h < 0:
        e = e0 + h / (1 - ksE)
        h = F(0)
    J = dict(I); J["x0"] = (a, e); J["h0"] = h
    return J


def grid_points(I):
    a0, e0 = I["x0"]
    amax = a0 + (I["h0"] + e0 * (1 - I["ks"][1])) / (1 + I["kb"][0])
    pts = {F(k, 20) for k in range(0, 40) if F(k, 20) < amax}
    return sorted(pts | {a0, amax})


def grid(k):
    I = build(k)
    pts = grid_points(I)
    out = []
    for a in pts:
        J = reduced(I, a)
        B = bayes(J)
        out.append(dict(a=float(a), E=cell(J, B, "E", "E"), N=cell(J, B, "E", "N")))
    return dict(k, grid=out)


def run_grid():
    ks = instances()
    res = []
    with Pool(8) as p:
        for i, r in enumerate(p.imap(grid, ks, chunksize=1)):
            res.append(r)
            if i % 50 == 0:
                print(f"grid {i}/{len(ks)}", flush=True)
    json.dump(res, open(HERE / "red_grid.json", "w"))


def direction(x):
    return "buy" if x > 1e-7 else "sell" if x < -1e-7 else "none"


def channel(r, tau):
    c = r["cells"]
    if any(c[k] is None or c[k]["lo"] is None for k in ("FE", "EE", "FN", "EN")):
        return None
    lo = c["FE"]["lo"] - c["EE"]["hi"] - c["FN"]["hi"] + c["EN"]["lo"] - 4 * tau
    hi = c["FE"]["hi"] - c["EE"]["lo"] - c["FN"]["lo"] + c["EN"]["hi"] + 4 * tau
    return lo, hi


def report():
    res = json.load(open(HERE / "red_stage1.json"))
    inv = max(c["inv"] for r in res for c in r["cells"].values() if c and c["inv"] is not None)
    tau = 10 * inv
    missing = sum(1 for r in res for c in r["cells"].values() if c is None or c["lo"] is None)
    print(f"instances {len(res)}; largest inversion {inv:.3e} bp; tau {tau:.3e} bp; missing brackets {missing}")
    tally, funded, exc = {}, {"match": 0, "exception": 0, "unresolved": 0, "noprediction": 0}, []
    for r in res:
        ch = channel(r, 0.0)
        # widen each cell bracket by tau: equivalent to +-4 tau on the sum
        if ch is not None:
            ch = (ch[0] - 4 * tau, ch[1] + 4 * tau)
        sg = None if ch is None else ("+" if ch[0] > 0 else "-" if ch[1] < 0 else "?")
        dF, dN = direction(r["cells"]["FE"]["uA"]), direction(r["cells"]["FN"]["uA"])
        td = dF if dF == dN else "split"
        key = (r["fam"], td, sg)
        tally[key] = tally.get(key, 0) + 1
        d = r["cells"]["FE"]["adj"] - r["cells"]["EN"]["adj"]
        pred = None if abs(d) < 1e-6 else ("+" if d > 0 else "-")
        if pred is None:
            funded["noprediction"] += 1
        elif sg == "?" or sg is None:
            funded["unresolved"] += 1
        elif sg == pred:
            funded["match"] += 1
        else:
            funded["exception"] += 1
            exc.append((r["fam"], r["cost"], r["tilt"], r["rho"], r["a0"], ch, r["cells"]["FE"]["adj"], r["cells"]["EN"]["adj"]))
        r["sign"], r["td"], r["ch"] = sg, td, ch
    for k in sorted(tally):
        print("  ", k, tally[k])
    print("funded rule:", funded)
    for e in exc:
        print("   exception", e[0], e[1], e[2], "rho", e[3], "a0", e[4], f"channel [{e[5][0]:+.3f}, {e[5][1]:+.3f}]",
              f"adj A_E {e[6]:.4f} B_N {e[7]:.4f}")
    json.dump(res, open(HERE / "red_stage1.json", "w"))


def grid_report():
    res = json.load(open(HERE / "red_stage1.json"))
    gr = json.load(open(HERE / "red_grid.json"))
    allb = [c for r in res for c in r["cells"].values() if c] + [g[R] for r in gr for g in r["grid"] for R in "EN" if g[R]]
    inv = max(c["inv"] for c in allb if c["inv"] is not None)
    tau = 10 * inv
    missing = [(r["fam"], r["cost"], r["rho"], r["a0"], g["a"], R) for r in gr for g in r["grid"] for R in "EN"
               if g[R] is None or g[R]["lo"] is None]
    print(f"grid brackets {sum(len(r['grid']) * 2 for r in gr)}; tau over all {tau:.3e} bp; missing {len(missing)}")
    for m in missing:
        print("   missing", m)
    worst_a0 = 0.0
    cls_whole, cls_local, pred = {}, {}, {}
    sc = {"INST_A": [0, 0], "012": [0, 0]}
    for r, g1 in zip(res, gr):
        assert (r["fam"], r["cost"], r["tilt"], r["a0"], r["rho"]) == (g1["fam"], g1["cost"], g1["tilt"], g1["a0"], g1["rho"])
        a0 = float(F(r["a0"])) if r["fam"] != "012 own" else 0.0
        G = g1["grid"]
        for g in G:
            if abs(g["a"] - a0) < 1e-12:
                worst_a0 = max(worst_a0, abs(g["E"]["pt"] - r["cells"]["EE"]["pt"]), abs(g["N"]["pt"] - r["cells"]["EN"]["pt"]))
        ok = [g["E"] is not None and g["E"]["lo"] is not None and g["N"] is not None and g["N"]["lo"] is not None for g in G]
        Gi = [(g["E"]["lo"] - g["N"]["hi"] - 2 * tau, g["E"]["hi"] - g["N"]["lo"] + 2 * tau) if o else None for g, o in zip(G, ok)]
        steps = []
        for k in range(len(G) - 1):
            if Gi[k] is None or Gi[k + 1] is None:
                steps.append("?")
            else:
                lo, hi = Gi[k + 1][0] - Gi[k][1], Gi[k + 1][1] - Gi[k][0]
                steps.append("+" if lo > 0 else "-" if hi < 0 else "?")
        def classify(st):
            p_, m_ = "+" in st, "-" in st
            return "not monotone" if p_ and m_ else "increasing" if p_ else "decreasing" if m_ else "unresolved"
        cw = classify(steps)
        tE, tN = a0 + r["cells"]["FE"]["uA"], a0 + r["cells"]["FN"]["uA"]
        lo_, hi_ = min(a0, tE, tN), max(a0, tE, tN)
        A = [g["a"] for g in G]
        i0 = max([i for i, a in enumerate(A) if a <= lo_ + 1e-12], default=0)
        i1 = min([i for i, a in enumerate(A) if a >= hi_ - 1e-12], default=len(A) - 1)
        if i1 <= i0:
            i1 = min(i0 + 1, len(A) - 1); i0 = i1 - 1
        cl = classify(steps[i0:i1])
        fam = "INST_A" if r["fam"] == "INST_A" else "012"
        cls_whole[(r["fam"], cw)] = cls_whole.get((r["fam"], cw), 0) + 1
        cls_local[(r["fam"], cl)] = cls_local.get((r["fam"], cl), 0) + 1
        # single crossing, both orientations, over all grid pairs
        for i in range(len(G)):
            for j in range(i + 1, len(G)):
                if not (ok[i] and ok[j]):
                    continue
                Ei, Ej, Ni, Nj = G[i]["E"], G[j]["E"], G[i]["N"], G[j]["N"]
                nup = Nj["lo"] - Ni["hi"] - 2 * tau > 0; ndn = Nj["hi"] - Ni["lo"] + 2 * tau < 0
                eup = Ej["lo"] - Ei["hi"] - 2 * tau > 0; edn = Ej["hi"] - Ei["lo"] + 2 * tau < 0
                sc[fam][0] += nup and edn; sc[fam][1] += ndn and eup
        # increasing-differences prediction
        for lab, c in (("whole", cw), ("local", cl)):
            td = r["td"]
            if c not in ("increasing", "decreasing") or td == "split":
                v = "no prediction"
            else:
                sgn = (1 if c == "increasing" else -1) * {"buy": 1, "sell": -1, "none": 0}[td]
                ps = "+" if sgn > 0 else "-" if sgn < 0 else "0"
                if r["sign"] == "?":
                    v = "match (zero)" if ps == "0" else "unresolved"
                else:
                    v = "match" if ps == r["sign"] else "mismatch"
            pred[(r["fam"], lab, v)] = pred.get((r["fam"], lab, v), 0) + 1
    print(f"largest |W_R(a0) - CE_(E,R)| {worst_a0:.2e} bp")
    print("G over the whole grid:", dict(sorted(cls_whole.items())))
    print("G over the local range:", dict(sorted(cls_local.items())))
    print("single-crossing violations (upward, downward):", sc)
    print("increasing-differences prediction:", dict(sorted(pred.items())))
    own = [(r["cost"], r["rho"], [(round(g["a"], 3), round(g["E"]["pt"] - g["N"]["pt"], 1)) for g in g1["grid"] if g["a"] in (0.0, 0.1, 0.15, 0.2, 0.25, 0.3, 0.45, 0.5)])
           for r, g1 in zip(res, gr) if r["fam"] == "012 own" and r["cost"] == "zero" and r["rho"] in ("5", "10", "20")]
    for o in own:
        print("   own incumbent G(a) (bp), zero costs, rho", o[1], o[2])


def switches():
    res = json.load(open(HERE / "red_stage1.json"))
    rows = {}
    for r in res:
        if r["fam"] != "INST_A":
            continue
        rows.setdefault((r["cost"], r["tilt"], r["a0"]), []).append((F(r["rho"]), r["sign"]))
    for key in sorted(rows, key=lambda k: (k[0], k[1], F(k[2]))):
        seq = sorted(rows[key])
        sw = [f"{float(seq[i][0])}-{float(seq[i + 1][0])}" for i in range(len(seq) - 1) if {seq[i][1], seq[i + 1][1]} == {"+", "-"}]
        print(f"   {key[0]:11s} tilt {key[1]:5s} a0 {float(F(key[2])):.2f}: " + "".join(x[1] for x in seq) + f"  switch {sw}")


def crossing_points():
    res = json.load(open(HERE / "red_stage1.json"))
    groups = {}
    for r in res:
        if r["cost"] == "zero":
            continue
        fam = "INST_A" if r["fam"] == "INST_A" else "012"
        groups.setdefault((fam, r["cost"], r["tilt"], r["rho"]), []).append(r)
    pts = []
    for key, rs in groups.items():
        edges = {}
        for R in "NE":
            a0s = [float(F(r["a0"])) for r in rs]
            buy = [a + r["cells"]["F" + R]["uA"] for a, r in zip(a0s, rs) if r["cells"]["F" + R]["uA"] > 1e-7]
            sell = [a + r["cells"]["F" + R]["uA"] for a, r in zip(a0s, rs) if r["cells"]["F" + R]["uA"] < -1e-7]
            edges[R] = (float(np.median(buy)) if buy else None, float(np.median(sell)) if sell else None)
        for side in (0, 1):
            x, y = edges["N"][side], edges["E"][side]
            if x is None or y is None or abs(x - y) <= 1e-4:
                continue
            lo, hi = min(x, y), max(x, y)
            for j in range(1, 6):
                pts.append(dict(fam=key[0], cost=key[1], tilt=key[2], rho=key[3], a0=lo + (hi - lo) * j / 6))
    return pts


def crossing(k):
    rho = F(k["rho"])
    a0 = F(k["a0"]).limit_denominator(10 ** 9)
    I = inst_a(a0, "INST_A-like", F(k["tilt"]), rho) if k["fam"] == "INST_A" else inst_012(a0, "1/100", rho)
    B = bayes(I)
    out = dict(k, cells={f"{D}{R}": cell(I, B, D, R) for D, R in CELLS})
    for R in "NE":
        V, u0 = R8.solve(I, B, "E", R)
        if V is None:
            V, u0 = R8.solve(I, B, "E", R, solver="SCS", eps_abs=1e-10, eps_rel=1e-10, max_iters=200000)
        try:
            b = R8.bracket(I, B, "F", R, u0, R8.SOL[0])
            out["Fat" + R] = max(b[0], b[1])
        except Exception:
            out["Fat" + R] = None
    return out


def run_crossings():
    pts = crossing_points()
    print(f"crossing search points: {len(pts)} ({sum(p['fam'] == 'INST_A' for p in pts)} INST_A)", flush=True)
    with Pool(8) as p:
        res = list(p.imap(crossing, pts, chunksize=1))
    json.dump(res, open(HERE / "red_crossings.json", "w"))
    tau = 8.289e-3
    n = {}
    for r in res:
        c = r["cells"]
        D = {}
        for R in "NE":
            lo = c["F" + R]["lo"] - c["E" + R]["hi"] - 2 * tau
            ub = None if r["Fat" + R] is None else r["Fat" + R] - c["E" + R]["lo"]
            D[R] = ">0" if lo > 0 else "0" if ub is not None and ub <= 1e-3 else "?"
            D[R + "v"] = (lo + 2 * tau, ub)
        typ = "cross E=0<N" if D["E"] == "0" and D["N"] == ">0" else "cross N=0<E" if D["N"] == "0" and D["E"] == ">0" else \
            f"N {D['N']} E {D['E']}"
        n[(r["fam"], typ)] = n.get((r["fam"], typ), 0) + 1
        if typ.startswith("cross"):
            print(f"   {typ} {r['fam']} tilt {r['tilt']} rho {r['rho']} a0 {r['a0']:.4f}: Delta_N >= {D['Nv'][0]:.4f} bp, "
                  f"Delta_E <= {D['Ev'][1]:.1e} bp")
    print("crossing classification:", dict(sorted(n.items())))


def premia_one(r):
    from check import nested, bp
    I = build(r); B = bayes(I)
    rho = I["rho"]
    phi = {}
    for name, cellkey in (("A_N", "FN"), ("A_E", "FE"), ("B_N", "EN"), ("B_E", "EE")):
        c = r["cells"][cellkey]
        u0 = np.array([c["uA"], c["uE"]])
        phi[name] = bp(nested(I, B, "E", u0), rho) - bp(nested(I, B, "N", u0), rho)
    return r, phi


def premia():
    res = json.load(open(HERE / "red_stage1.json"))
    pick = [r for r in res if r["fam"] != "INST_A" and r["sign"] == "+" and r["td"] == "buy"]
    pick += [r for r in res if r["fam"] == "INST_A" and r["td"] == "split" and r["rho"] in ("5", "10") and r["sign"] == "-"]
    with Pool(8) as p:
        out = p.map(premia_one, pick)
    for r, ph in out:
        lo, hi = r["ch"]
        sw = ph["A_N"] - ph["B_E"] <= hi + 0.2 and lo - 0.2 <= ph["A_E"] - ph["B_N"]
        print(f"   {r['fam']:8s} {r['cost']:11s} tilt {r['tilt']:5s} rho {r['rho']:>4} a0 {r['a0']:>6}: channel [{lo:+.3f}, {hi:+.3f}] "
              f"phi A_N {ph['A_N']:.2f} A_E {ph['A_E']:.2f} B_N {ph['B_N']:.2f} B_E {ph['B_E']:.2f}; sandwich {'holds' if sw else 'FAILS'}")


if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "stage1"
    if what == "stage1":
        run_stage1()
    elif what == "gridreport":
        grid_report()
    elif what == "switches":
        switches()
    elif what == "crossings":
        run_crossings()
    elif what == "premia":
        premia()
    elif what == "grid":
        run_grid()
    elif what == "report":
        report()
    elif what == "one":
        import time
        t = time.time(); r = stage1(instances()[int(sys.argv[2])]); print(r, time.time() - t)
