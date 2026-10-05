"""Red's independent reproduction of experiment 007, plus the attribution attacks math asked for.

Written from the registered Design without reading experiments/007/run.py. The candidate optima come
from the registered exact reference solver (experiments/004/m2.py, as the Design prescribes). Every
other element is red's own code, and every F and E answer must pass red's exact directional KKT
certificate (as in red's reproductions of 004 and 005):
the grid, Sigma by scenario enumeration, the mean vector, the certificate, claim 009's band read
literally from its Statement, the return-positive domain J, the boundary probes, the H1-H3 pair tests
and the tables. The script then compares every row with experiments/007/results.json.

Attacks (math's d2-boundary-reading note):
  A1  H2 attribution: the budget multiplier at the F optimum in each violating pair, and two
      counterfactuals that leave cash untouched. In the first, the ETF sale rate is set to zero
      (the "sale leg"). In the second, lambda_2 = 0 (so the active fund no longer carries the only
      or cheapest factor-2 premium).
  A2  Binding cash versus a positive multiplier, at the E optimum that defines the band.
  A3  Full versus positivity-clipped widths: J and every finite endpoint.
  A4  What the active trade at alpha-bar = 0 buys: mean returns and the lambda_2 = 0 counterfactual.

Usage: uv run python experiments/007/red_reproduce.py
"""
import itertools
import json
import sys
from collections import Counter, defaultdict
from dataclasses import replace
from fractions import Fraction as Fr
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "004"))
from m2 import Instance2, solve  # noqa: E402  (registered reference solver: candidates only)

INF = None
ONE_ETF = ((Fr(1), Fr(0)),)
TWO_ETF = ((Fr(1), Fr(0)), (Fr(1), Fr(1, 4)))
COSTS = [  # name, active (buy, sell), each ETF (buy, sell)
    ("Zero", (Fr(0), Fr(0)), (Fr(0), Fr(0))),
    ("Equal low", (Fr(1, 2000), Fr(1, 2000)), (Fr(1, 2000), Fr(1, 2000))),
    ("Equal medium", (Fr(1, 500), Fr(1, 500)), (Fr(1, 500), Fr(1, 500))),
    ("Equal high", (Fr(1, 100), Fr(1, 100)), (Fr(1, 100), Fr(1, 100))),
    ("Equal, asymmetric directions", (Fr(1, 2000), Fr(1, 500)), (Fr(1, 2000), Fr(1, 500))),
    ("Active costlier (sensitivity)", (Fr(1, 500), Fr(1, 250)), (Fr(1, 2000), Fr(1, 2000))),
    ("ETF costlier", (Fr(1, 2000), Fr(1, 2000)), (Fr(1, 500), Fr(1, 250))),
]
A0S = [Fr(0), Fr(1, 2), Fr(1)]
CS = [Fr(0), Fr(1, 4), Fr(1, 2), Fr(3, 4), Fr(1)]
DS = [Fr(0), Fr(1, 4), Fr(1, 2), Fr(1)]
PRIOR = [(l1, Fr(1, 200), al) for l1 in (Fr(3, 200), Fr(1, 40)) for al in (Fr(-1, 400), Fr(1, 400))]
LAM_BAR = (sum(t[0] for t in PRIOR) / 4, Fr(1, 200))
ALPHA_BAR = sum(t[2] for t in PRIOR) / 4
E8 = Fr(1, 10 ** 8)


def instance(menu, a0, c, d, cost, lam=LAM_BAR, etf_sell=None, etf_buy=None):
    BE = ONE_ETF if menu == 1 else TWO_ETF
    n = len(BE)
    k0 = (1 - a0) * c
    p = [(1 - a0) * (1 - c) / n] * n
    (ab, as_), (eb, es) = cost[1], cost[2]
    if etf_sell is not None:
        es = etf_sell
    if etf_buy is not None:
        eb = etf_buy
    return Instance2(BA=(Fr(1), Fr(1, 2)), BE=BE, sf=(Fr(3, 50), Fr(1, 50)), sA=Fr(3, 100),
                     sE=(Fr(1, 200), Fr(1, 100))[:n], lam=lam, alpha=ALPHA_BAR,
                     cE=(Fr(-1, 10000), Fr(0))[:n], gamma=Fr(1),
                     kbuy=(ab,) + (eb,) * n, ksell=(as_,) + (es,) * n,
                     w0=(a0, *p), k0=k0, wbar=(Fr(1), *[pj + d * (1 - pj) for pj in p]))


# ------------------------------------------------------------------ red's own M2 objects
def loadings(I):
    return [I.BA] + list(I.BE)


def mean(I):
    return [I.BA[0] * I.lam[0] + I.BA[1] * I.lam[1] + I.alpha] + \
           [b[0] * I.lam[0] + b[1] * I.lam[1] - c for b, c in zip(I.BE, I.cE)]


def scenarios(I):
    """32 equiprobable sign scenarios over (f1, f2, active, ETF1, ETF2); the fifth sign is unused
    with one ETF, which leaves each scenario's law unchanged and every shock centered."""
    sizes = [Fr(3, 50), Fr(1, 50), Fr(3, 100), Fr(1, 200), Fr(1, 100)]
    B, d = loadings(I), 1 + len(I.BE)
    for sg in itertools.product((-1, 1), repeat=5):
        z = [s * x for s, x in zip(sg, sizes)]
        yield [B[i][0] * z[0] + B[i][1] * z[1] + z[2 + i] for i in range(d)]


def sigma(I):
    d = 1 + len(I.BE)
    S = [[Fr(0)] * d for _ in range(d)]
    for xi in scenarios(I):
        for i in range(d):
            for j in range(d):
                S[i][j] += xi[i] * xi[j] / 32
    return S


def cost_of(I, w):
    return sum(I.kbuy[i] * max(w[i] - I.w0[i], 0) + I.ksell[i] * max(I.w0[i] - w[i], 0) for i in range(len(w)))


def cash(I, w):
    return I.k0 - sum(w[i] - I.w0[i] for i in range(len(w))) - cost_of(I, w)


def score(I, mu, S, w):
    d = len(w)
    return sum(mu[i] * w[i] for i in range(d)) - I.gamma / 2 * sum(
        w[i] * S[i][j] * w[j] for i in range(d) for j in range(d)) - cost_of(I, w)


def eta_interval(I, mu, S, w, skip):
    """Exact interval [lo, hi] (hi None = +inf) of budget multipliers compatible with the directional
    KKT conditions of the coordinates not in skip; lo > hi means none."""
    d = len(w)
    g = [mu[i] - I.gamma * sum(S[i][j] * w[j] for j in range(d)) for i in range(d)]
    lo, hi = Fr(0), (None if cash(I, w) == 0 else Fr(0))
    for i in range(d):
        if i in skip:
            continue
        if w[i] > I.w0[i]:
            zmin = zmax = I.kbuy[i]
        elif w[i] < I.w0[i]:
            zmin = zmax = -I.ksell[i]
        else:
            zmin, zmax = -I.ksell[i], I.kbuy[i]
        if w[i] != 0:
            ub = (g[i] - zmin) / (1 + zmin)
            hi = ub if hi is None else min(hi, ub)
        if w[i] != I.wbar[i]:
            lo = max(lo, (g[i] - zmax) / (1 + zmax))
    return lo, hi, g


def certified_opt(I, cls, S=None):
    """Registered solver's candidate, accepted only with red's certificate and a value check."""
    V, w, _ = solve(I, cls, exact=True)
    w = list(w)
    mu, S = mean(I), (S or sigma(I))
    feas = all(0 <= w[i] <= I.wbar[i] for i in range(len(w))) and cash(I, w) >= 0 and \
        (cls != "E" or w[0] == I.w0[0])
    lo, hi, _ = eta_interval(I, mu, S, w, {0} if cls == "E" else set())
    ok = feas and (hi is None or lo <= hi) and score(I, mu, S, w) == V
    return w, V, ok, (lo, hi)


def band009(I, wE, S):
    """Claim 009's Statement, literally: alpha_c, the compatible multipliers I = [lo, hi] at the
    certified E optimum, and the no-active-trade set C in alpha (None = infinite endpoint)."""
    mu, n = mean(I), len(I.BE)
    Sw = [sum(S[i][j] * wE[j] for j in range(1 + n)) for i in range(1 + n)]
    alpha_c = I.gamma * Sw[0] - (I.BA[0] * I.lam[0] + I.BA[1] * I.lam[1])
    if cash(I, wE) > 0:
        lo = hi = Fr(0)
    else:
        lows, highs = [Fr(0)], []
        for j in range(n):
            pj, p0, pb = wE[1 + j], I.w0[1 + j], I.wbar[1 + j]
            if pb == 0:
                continue
            kp, km = I.kbuy[1 + j], I.ksell[1 + j]
            ell, u = (kp, kp) if pj > p0 else ((-km, -km) if pj < p0 else (-km, kp))
            gj = mu[1 + j] - I.gamma * Sw[1 + j]
            if pj < pb:
                lows.append((gj - u) / (1 + u))
            if pj > 0:
                highs.append((gj - ell) / (1 + ell))
        lo, hi = max(lows), (min(highs) if highs else None)
    b, s, a0 = I.kbuy[0], I.ksell[0], I.w0[0]
    L = alpha_c - s + (1 - s) * lo
    U = None if hi is None else alpha_c + b + (1 + b) * hi
    C = (L if a0 > 0 else None, U if a0 < I.wbar[0] else None)
    width = None if (C[0] is None or C[1] is None) else C[1] - C[0]
    terms = None if width is None else (b * (1 + hi), s * (1 + lo), hi - lo)
    return dict(alpha_c=alpha_c, lo=lo, hi=hi, C=C, width=width, terms=terms)


def in_C(C, x):
    return (C[0] is None or C[0] <= x) and (C[1] is None or x <= C[1])


def J_lower(I):
    """Open lower end of the translated-alpha domain: every support point (lambda, alpha - bar alpha + t)
    and scenario must give a positive gross return for every instrument (ETFs do not depend on t)."""
    worst = None
    for xi in scenarios(I):
        for l1, l2, al in PRIOR:
            m = I.BA[0] * l1 + I.BA[1] * l2 + (al - ALPHA_BAR)
            v = -(1 + m + xi[0])        # need t > v
            worst = v if worst is None else max(worst, v)
            for j, (bj, cj) in enumerate(zip(I.BE, I.cE)):
                assert 1 + bj[0] * l1 + bj[1] * l2 - cj + xi[1 + j] > 0
    return worst


def fs(x):
    return None if x is None else f"{Fr(x).numerator}/{Fr(x).denominator}"


def pct(x):
    return f"{float(x) * 1e4:.3f}"


def median(xs):
    ys = sorted(xs)
    n = len(ys)
    return (ys[n // 2 - 1] + ys[n // 2]) / 2 if n % 2 == 0 else ys[n // 2]


# ------------------------------------------------------------------ the registered grid
def main():
    fails = []
    S = {m: sigma(instance(m, Fr(1, 2), Fr(1, 2), Fr(1), COSTS[0])) for m in (1, 2)}
    for m in (1, 2):
        if not sp.Matrix(S[m]).is_positive_definite:
            fails.append(f"menu {m}: Sigma not positive definite")
    if S[1][0][0] != S[2][0][0] or S[1][0][1] != S[2][0][1] or S[1][1][1] != S[2][1][1]:
        fails.append("shared instruments differ in law across menus")
    Jlo = {m: J_lower(instance(m, Fr(1, 2), Fr(1, 2), Fr(1), COSTS[0])) for m in (1, 2)}
    print(f"belief mean {LAM_BAR}, {ALPHA_BAR}; J lower (open): menu 1 {Jlo[1]}, menu 2 {Jlo[2]}")

    rows = {}
    for m, a0, c, d, (ci, cost) in itertools.product((1, 2), A0S, CS, DS, enumerate(COSTS)):
        I = instance(m, a0, c, d, cost)
        wF, VF, okF, etaF = certified_opt(I, "F", S[m])
        wE, VE, okE, etaE = certified_opt(I, "E", S[m])
        VN = score(I, mean(I), S[m], list(I.w0))
        bd = band009(I, wE, S[m])
        rows[m, a0, c, d, cost[0]] = dict(I=I, wF=wF, wE=wE, VF=VF, VE=VE, VN=VN, ok=okF and okE, etaF=etaF,
                                          etaE=etaE, band=bd, trade=wF[0] - a0, ci=ci)
        if not (okF and okE):
            fails.append(f"certificate failed {m, a0, c, d, cost[0]}")
        if (bd["lo"], bd["hi"]) != etaE:
            fails.append(f"claim 009 I differs from red's E certificate {m, a0, c, d, cost[0]}")
        if in_C(bd["C"], ALPHA_BAR) != (wF[0] == a0):
            fails.append(f"claim 009 C mispredicts F {m, a0, c, d, cost[0]}")
    distinct = len({(r["I"].w0, r["I"].k0, r["I"].wbar, r["I"].kbuy, r["I"].ksell, len(r["I"].BE))
                    for r in rows.values()})
    print(f"rows {len(rows)}; distinct states {distinct}; certified F and E: {sum(r['ok'] for r in rows.values())}")

    # Boundary probes: each finite endpoint and +-1e-8, alpha support translated together.
    probes = agree = outside = 0
    for key, r in rows.items():
        I, C = r["I"], r["band"]["C"]
        for e in (C[0], C[1]):
            if e is None:
                continue
            for x in (e - E8, e, e + E8):
                if not x > Jlo[key[0]]:
                    outside += 1
                    continue
                K = replace(I, alpha=x)
                w, _, ok, _ = certified_opt(K, "F", S[key[0]])
                probes += 1
                agree += ok and ((w[0] == I.w0[0]) == in_C(C, x))
    print(f"boundary probes {probes}, certified and agreeing with C {agree}, outside J {outside}")
    if agree != probes:
        fails.append("boundary probe disagreement")

    # Compare with the reported results.json, row by row, exactly.
    rep = {(r["menu"], Fr(r["a0"]), Fr(r["c"]), Fr(r["d"]), r["cost"]): r
           for r in json.load(open(HERE / "results.json"))["rows"]}
    mism = Counter()
    for k, r in rows.items():
        q = rep[k]
        bd = r["band"]
        checks = {
            "F holdings": [fs(x) for x in r["wF"]] == q["F"]["holdings"],
            "E holdings": [fs(x) for x in r["wE"]] == q["E"]["holdings"],
            "VF-VE": fs(r["VF"] - r["VE"]) == q["VF_minus_VE"],
            "VE-VN": fs(r["VE"] - r["VN"]) == q["VE_minus_VN"],
            "I": [fs(bd["lo"]), fs(bd["hi"])] == [x if x != "inf" else None for x in q["claim009"]["I"]],
            "C": [fs(x) for x in bd["C"]] == [None if x in ("-inf", "inf") else x for x in q["claim009"]["C"]],
            "alpha_c": fs(bd["alpha_c"]) == q["claim009"]["alpha_c"],
            "F eta": [fs(x) for x in r["etaF"]] == [None if x == "inf" else x for x in q["F"]["eta"]],
        }
        for name, ok in checks.items():
            mism[name] += not ok
    print("row-by-row mismatches against results.json:", dict(mism))
    if any(mism.values()):
        fails.append(f"results.json mismatches {dict(mism)}")

    # ------------------------------------------------------------ targets H1-H3
    def pairs_H1():
        for m, a0, c, (ci, cost) in itertools.product((1, 2), A0S, CS, enumerate(COSTS)):
            for d_hi, d_lo in zip(DS[1:], DS[:-1]):     # tightening: d_hi -> d_lo
                yield rows[m, a0, c, d_hi, cost[0]], rows[m, a0, c, d_lo, cost[0]]

    def pairs_H2():
        for m, a0, (ci, cost) in itertools.product((1, 2), A0S, enumerate(COSTS)):
            for c1, c2 in zip(CS[:-1], CS[1:]):
                yield rows[m, a0, c1, Fr(1), cost[0]], rows[m, a0, c2, Fr(1), cost[0]]

    def pairs_H3():
        sym = [x[0] for x in COSTS[:4]]
        for m, c, d in itertools.product((1, 2), CS, DS):
            for k1, k2 in zip(sym[:-1], sym[1:]):
                yield rows[m, Fr(1, 2), c, d, k1], rows[m, Fr(1, 2), c, d, k2]

    H1 = [(x, y) for x, y in pairs_H1() if abs(y["trade"]) < abs(x["trade"])]
    H2 = [(x, y) for x, y in pairs_H2() if abs(y["trade"]) > abs(x["trade"])]
    H3 = [(x, y) for x, y in pairs_H3() if y["band"]["width"] < x["band"]["width"]]
    print(f"H1 pairs {len(list(pairs_H1()))} violations {len(H1)}; H2 pairs {len(list(pairs_H2()))} violations "
          f"{len(H2)}; H3 pairs {len(list(pairs_H3()))} violations {len(H3)}")
    if (len(H1), len(H2), len(H3)) != (0, 88, 3):
        fails.append("target counts differ from the report (0, 88, 3)")
    if H2 and not all(abs(y["trade"]) > abs(x["trade"]) and y["I"].k0 > x["I"].k0 for x, y in H2):
        fails.append("H2 violation direction")
    for x, y in H3:
        k = lambda r: (r["I"].BE.__len__(), r["I"].k0, r["I"].wbar[1:])
        print(f"  H3 witness menu {len(x['I'].BE)}, c={x['I'].k0 * 2}, wbar_E={[str(v) for v in x['I'].wbar[1:]]}: "
              f"width {pct(x['band']['width'])} -> {pct(y['band']['width'])} bp; I {fs(x['band']['lo'])},"
              f"{fs(x['band']['hi'])} -> {fs(y['band']['lo'])},{fs(y['band']['hi'])}; E cash "
              f"{cash(x['I'], x['wE'])} -> {cash(y['I'], y['wE'])}; E ETF {[str(v) for v in x['wE'][1:]]} -> "
              f"{[str(v) for v in y['wE'][1:]]}")

    # ------------------------------------------------------------ tables
    print("\nPrimary panel a0 = 1/2: width and terms (bp), true median over the 20 (c, d) cells "
          "[reported value is the median of 20; true median shown]")
    for m, (ci, cost) in itertools.product((1, 2), enumerate(COSTS)):
        rs = [rows[m, Fr(1, 2), c, d, cost[0]] for c in CS for d in DS]
        W = [r["band"]["width"] for r in rs]
        T = list(zip(*[r["band"]["terms"] for r in rs]))
        print(f"  menu {m} {cost[0]:32s} width {pct(median(W))} terms {pct(median(T[0]))} {pct(median(T[1]))} "
              f"{pct(median(T[2]))}; hi>lo rows {sum(t > 0 for t in T[2])}; active trade rows "
              f"{sum(r['trade'] != 0 for r in rs)}")
    print("\nCash sweep d = 1, a0 = 1/2: |active trade| by c")
    for m, (ci, cost) in itertools.product((1, 2), enumerate(COSTS)):
        print(f"  menu {m} {cost[0]:32s}", " ".join(f"{float(abs(rows[m, Fr(1, 2), c, Fr(1), cost[0]]['trade'])):.4f}"
                                                   for c in CS))
    print("\nCap sweep a0 = 1/2, c = 1/2: |active trade| by d")
    for m, (ci, cost) in itertools.product((1, 2), enumerate(COSTS)):
        print(f"  menu {m} {cost[0]:32s}", " ".join(f"{float(abs(rows[m, Fr(1, 2), Fr(1, 2), d, cost[0]]['trade'])):.4f}"
                                                   for d in DS))
    unpinned = sum(1 for k, r in rows.items() if k[1] == Fr(1, 2) and r["band"]["hi"] is not None
                   and r["band"]["hi"] > r["band"]["lo"])
    print(f"primary-panel rows with hi > lo: {unpinned} of 280")

    # ------------------------------------------------------------ A1: H2 attribution
    print("\nA1. H2 attribution (the 88 violating pairs)")
    lowc = [x for x, _ in H2]
    cash0 = sum(cash(x["I"], x["wF"]) == 0 for x in lowc)
    zero_ok = sum(x["etaF"][0] == 0 for x in lowc)
    pos = sum(x["etaF"][0] > 0 for x in lowc)
    print(f"  lower-cash state F optimum: cash 0 in {cash0}; multiplier interval contains 0 in {zero_ok}; "
          f"multiplier forced positive in {pos}")
    for label, kw in (("ETF sale rate set to 0", dict(etf_sell=Fr(0))),
                      ("ETF costless both ways (cash acts only through funding)", dict(etf_sell=Fr(0), etf_buy=Fr(0))),
                      ("lambda_2 = 0", dict(lam=(LAM_BAR[0], Fr(0))))):
        viol = tot = flat = 0
        for m, a0, (ci, cost) in itertools.product((1, 2), A0S, enumerate(COSTS)):
            tr = []
            for c in CS:
                K = instance(m, a0, c, Fr(1), cost, **kw)
                w, _, ok, _ = certified_opt(K, "F")
                if not ok:
                    fails.append(f"A1 certificate failed ({label})")
                tr.append(abs(w[0] - a0))
            tot += 4
            viol += sum(t2 > t1 for t1, t2 in zip(tr, tr[1:]))
            flat += sum(t2 == t1 for t1, t2 in zip(tr, tr[1:]))
        print(f"  counterfactual {label}: H2 violations {viol} of {tot} pairs; unchanged |trade| in {flat}")

    tot = allin = 0
    for m, a0, (ci, cost) in itertools.product((1, 2), A0S[:2], enumerate(COSTS[1:])):
        for c in CS[1:]:
            r = rows[m, a0, c, Fr(1), cost[0]]
            tot += 1
            allin += r["wF"][1:] == list(r["I"].w0[1:]) and cash(r["I"], r["wF"]) == 0 and r["trade"] > 0
    print(f"  cash sweep, positive costs, a0 < 1, c > 0: F spends all cash on the active fund and leaves "
          f"every ETF untouched in {allin} of {tot} states")

    # ------------------------------------------------------------ A2: binding cash vs positive multiplier
    print("\nA2. At the certified E optimum (the band's base point), all 840 rows")
    tab = Counter()
    for r in rows.values():
        kE, lo, hi = cash(r["I"], r["wE"]), r["band"]["lo"], r["band"]["hi"]
        tab["cash > 0 (lo = hi = 0)" if kE > 0 else
            ("cash 0, multiplier forced positive (lo > 0)" if lo > 0 else "cash 0, zero multiplier compatible (lo = 0)")] += 1
    for k, v in sorted(tab.items()):
        print(f"  {k}: {v}")

    # ------------------------------------------------------------ A3: clipped widths
    fin = [(k, e) for k, r in rows.items() for e in r["band"]["C"] if e is not None]
    print(f"\nA3. finite endpoints {len(fin)}; inside J {sum(e > Jlo[k[0]] for k, e in fin)}; "
          f"rows with a finite width {sum(r['band']['width'] is not None for r in rows.values())} (all a0 = 1/2); "
          f"rays (a0 in {{0,1}}) {sum(r['band']['width'] is None for r in rows.values())}")

    # ------------------------------------------------------------ A4: what the trade buys
    mu1, mu2 = mean(instance(1, 0, 0, 1, COSTS[0])), mean(instance(2, 0, 0, 1, COSTS[0]))
    print(f"\nA4. means at the belief mean: active {mu1[0]}, ETF1 {mu1[1]}, ETF2 {mu2[2]}; "
          f"active trades at alpha-bar: {sum(r['trade'] != 0 for r in rows.values())} of 840, purchases "
          f"{sum(r['trade'] > 0 for r in rows.values())}")
    zero = Counter()
    for k, r in rows.items():
        K = instance(k[0], k[1], k[2], k[3], COSTS[r["ci"]], lam=(LAM_BAR[0], Fr(0)))
        w, _, ok, _ = certified_opt(K, "F")
        zero["trade" if w[0] != k[1] else "none"] += 1
        zero["purchase"] += w[0] > k[1]
    print(f"  lambda_2 = 0 counterfactual: rows with an active trade {zero['trade']}, purchases {zero['purchase']}")

    print(f"\nFailures: {len(fails)}")
    for f in fails[:20]:
        print(" -", f)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
