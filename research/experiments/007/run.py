"""Experiment 007: M2 active intervention across ETF funding and position limits at fixed beliefs.
Design: experiments/007-m2-boundary-response.md (registered by math). Exact rational arithmetic only.

Components (all exact):
- instance construction from the registered grid, with Sigma from the 32 sign scenarios and positivity
  checked at every support point of the 4-point prior (not only at the mean);
- F and E optima from experiments/004/m2.py (exact mode), N directly;
- `certify`: an exact directional KKT certificate written here, independent of the solver's enumeration;
  it returns the interval of budget multipliers eta compatible with the candidate, or None;
- `claim009`: claim 009's formulas implemented literally from its Statement (g_E, alpha_c, ell/u, I, L, U,
  C, J), kept separate from `certify`;
- boundary probes at each finite band endpoint and +- 1/10^8 inside J;
- the three registered monotonicity targets H1-H3, exact inequalities, no tolerance.
Writes experiments/007/results.json and experiments/007/counterexamples.json; prints Markdown summaries.
"""
from __future__ import annotations

import json
import sys
import time
from dataclasses import replace
from fractions import Fraction as Fr
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "004"))
from m2 import Instance2, objective, solve  # noqa: E402

INF = None                                   # explicit infinity marker in intervals
DELTA = Fr(1, 10 ** 8)
GAMMA = Fr(1)
BA = (Fr(1), Fr(1, 2))
MENUS = {1: ((Fr(1), Fr(0)),), 2: ((Fr(1), Fr(0)), (Fr(1), Fr(1, 4)))}
DRAG = (Fr(-1, 10000), Fr(0))
SF = (Fr(3, 50), Fr(1, 50))
SA = Fr(3, 100)
SE = (Fr(1, 200), Fr(1, 100))
PRIOR = [((l1, Fr(1, 200)), al) for l1 in (Fr(3, 200), Fr(1, 40)) for al in (Fr(-1, 400), Fr(1, 400))]
LAM_BAR = (sum(p[0][0] for p in PRIOR) / 4, sum(p[0][1] for p in PRIOR) / 4)
ALPHA_BAR = sum(p[1] for p in PRIOR) / 4
A0S = [Fr(0), Fr(1, 2), Fr(1)]
CS = [Fr(0), Fr(1, 4), Fr(1, 2), Fr(3, 4), Fr(1)]
DS = [Fr(0), Fr(1, 4), Fr(1, 2), Fr(1)]
COSTS = [  # name, (active buy, active sell), (ETF buy, ETF sell); all assumed
    ("Zero", (Fr(0), Fr(0)), (Fr(0), Fr(0))),
    ("Equal low", (Fr(1, 2000), Fr(1, 2000)), (Fr(1, 2000), Fr(1, 2000))),
    ("Equal medium", (Fr(1, 500), Fr(1, 500)), (Fr(1, 500), Fr(1, 500))),
    ("Equal high", (Fr(1, 100), Fr(1, 100)), (Fr(1, 100), Fr(1, 100))),
    ("Equal, asymmetric directions", (Fr(1, 2000), Fr(1, 500)), (Fr(1, 2000), Fr(1, 500))),
    ("Active costlier (sensitivity)", (Fr(1, 500), Fr(1, 250)), (Fr(1, 2000), Fr(1, 2000))),
    ("ETF costlier", (Fr(1, 2000), Fr(1, 2000)), (Fr(1, 500), Fr(1, 250))),
]
COST_ORDER = {c[0]: i for i, c in enumerate(COSTS)}


# ---------------------------------------------------------------- returns and admissibility
def scenario_xi(n: int):
    """32 equiprobable sign scenarios over (f1, f2, eA, eE1, eE2); the fifth sign is unused when n = 1."""
    out = []
    for s in product((1, -1), repeat=5):
        zf = (s[0] * SF[0], s[1] * SF[1])
        xa = BA[0] * zf[0] + BA[1] * zf[1] + s[2] * SA
        xe = [MENUS[n][j][0] * zf[0] + MENUS[n][j][1] * zf[1] + s[3 + j] * SE[j] for j in range(n)]
        out.append([xa] + xe)
    return out


def sigma_scen(n: int):
    X = scenario_xi(n)
    d = 1 + n
    return [[sum(x[i] * x[j] for x in X) / len(X) for j in range(d)] for i in range(d)]


def mu_at(n: int, lam, alpha):
    B = MENUS[n]
    return [BA[0] * lam[0] + BA[1] * lam[1] + alpha] + \
        [B[j][0] * lam[0] + B[j][1] * lam[1] - DRAG[j] for j in range(n)]


def positive_everywhere(n: int, shift=Fr(0)) -> bool:
    """Every gross return positive at every support point (alpha support translated by shift) and scenario."""
    X = scenario_xi(n)
    for lam, al in PRIOR:
        mu = mu_at(n, lam, al + shift)
        if any(1 + mu[i] + x[i] <= 0 for x in X for i in range(1 + n)):
            return False
    return True


def pos_def(S) -> bool:
    d = len(S)
    for k in range(1, d + 1):
        M = [[S[i][j] for j in range(k)] for i in range(k)]
        det = Fr(1)
        for c in range(k):
            p = next((r for r in range(c, k) if M[r][c] != 0), None)
            if p is None:
                return False
            if p != c:
                M[c], M[p] = M[p], M[c]
                det = -det
            det *= M[c][c]
            for r in range(c + 1, k):
                f = M[r][c] / M[c][c]
                M[r] = [a - f * b for a, b in zip(M[r], M[c])]
        if det <= 0:
            return False
    return True


def instance(n, a0, c, d, cost, x=None) -> Instance2:
    _, (ab, as_), (eb, es) = next(k for k in COSTS if k[0] == cost)
    k0 = (1 - a0) * c
    p0 = (1 - a0) * (1 - c) / n
    w0 = (a0,) + (p0,) * n
    wbar = (Fr(1),) + tuple(p0 + d * (1 - p0) for _ in range(n))
    return Instance2(BA=BA, BE=MENUS[n], sf=SF, sA=SA, sE=SE[:n], lam=LAM_BAR,
                     alpha=ALPHA_BAR if x is None else x, cE=DRAG[:n], gamma=GAMMA,
                     kbuy=(ab,) + (eb,) * n, ksell=(as_,) + (es,) * n, w0=w0, k0=k0, wbar=wbar)


# ---------------------------------------------------------------- exact certificate
def cash(I, w):
    v = [w[i] - I.w0[i] for i in range(I.d)]
    return I.k0 - sum(v) - sum(I.kbuy[i] * max(v[i], 0) + I.ksell[i] * max(-v[i], 0) for i in range(I.d))


def certify(I, S, w, cls):
    """Exact directional KKT certificate for max Qbar on class cls at w. Returns (lo, hi) of compatible
    budget multipliers (hi None = infinity), or None if w is infeasible or no multiplier works."""
    d = I.d
    if any(w[i] < 0 or w[i] > I.wbar[i] for i in range(d)) or cash(I, w) < 0:
        return None
    if cls == "E" and w[0] != I.w0[0]:
        return None
    mu = mu_at(I.n, I.lam, I.alpha)
    lo, hi = Fr(0), INF
    for i in range(d):
        if cls == "E" and i == 0:
            continue
        g = mu[i] - I.gamma * sum(S[i][j] * w[j] for j in range(d))
        v = w[i] - I.w0[i]
        smin, smax = ((I.kbuy[i], I.kbuy[i]) if v > 0 else (-I.ksell[i], -I.ksell[i]) if v < 0
                      else (-I.ksell[i], I.kbuy[i]))
        if w[i] < I.wbar[i]:          # g - eta <= (1+eta) smax  <=>  eta >= (g - smax)/(1 + smax)
            lo = max(lo, (g - smax) / (1 + smax))
        if w[i] > 0:                  # g - eta >= (1+eta) smin  <=>  eta <= (g - smin)/(1 + smin)
            b = (g - smin) / (1 + smin)
            hi = b if hi is INF else min(hi, b)
    if cash(I, w) > 0:                # complementary slackness forces eta = 0
        if lo > 0 or (hi is not INF and hi < 0):
            return None
        return (Fr(0), Fr(0))
    if hi is not INF and lo > hi:
        return None
    return (lo, hi)


# ---------------------------------------------------------------- claim 009, literally
def claim009(I, S, wE):
    n, d = I.n, I.d
    mu = mu_at(n, I.lam, I.alpha)
    Sw = [sum(S[i][j] * wE[j] for j in range(d)) for i in range(d)]
    gE = [mu[1 + j] - I.gamma * Sw[1 + j] for j in range(n)]
    alpha_c = I.gamma * Sw[0] - (BA[0] * I.lam[0] + BA[1] * I.lam[1])
    kE = cash(I, wE)
    ell, u = [], []
    for j in range(n):
        pe, pm = wE[1 + j], I.w0[1 + j]
        kb, ks = I.kbuy[1 + j], I.ksell[1 + j]
        ell.append(kb if pe > pm else -ks)
        u.append(kb if pe > pm else (-ks if pe < pm else kb))
    if kE > 0:
        lo, hi = Fr(0), Fr(0)
    else:
        lo = max([Fr(0)] + [(gE[j] - u[j]) / (1 + u[j]) for j in range(n) if wE[1 + j] < I.wbar[1 + j]
                            and I.wbar[1 + j] != 0])
        ups = [(gE[j] - ell[j]) / (1 + ell[j]) for j in range(n) if wE[1 + j] > 0 and I.wbar[1 + j] != 0]
        hi = min(ups) if ups else INF
    b, s = I.kbuy[0], I.ksell[0]
    a0, abar = I.w0[0], I.wbar[0]
    L = alpha_c - s + (1 - s) * lo
    U = alpha_c + b + (1 + b) * hi if hi is not INF else INF
    if 0 < a0 < abar:
        C = (L, U)
    elif a0 == 0 < abar:
        C = ("-inf", U)
    elif 0 < a0 == abar:
        C = (L, "inf")
    else:
        C = ("-inf", "inf")
    width_terms = None
    if 0 < a0 < abar and hi is not INF:
        width_terms = (b * (1 + hi), s * (1 + lo), hi - lo)
    return dict(gE=gE, alpha_c=alpha_c, kE=kE, ell=ell, u=u, lo=lo, hi=hi, L=L, U=U, C=C,
                width_terms=width_terms)


def alpha_min(n):
    X = scenario_xi(n)
    return max(-1 - (BA[0] * lam[0] + BA[1] * lam[1]) - al + ALPHA_BAR - x[0] for lam, al in PRIOR for x in X)


# ---------------------------------------------------------------- per-row computation
def q(x):
    if x is INF or x == "inf":
        return "inf"
    if x == "-inf":
        return "-inf"
    return f"{x.numerator}/{x.denominator}"


def row(n, a0, c, d, cost, S, amin):
    I = instance(n, a0, c, d, cost)
    rec = dict(menu=n, a0=q(a0), c=q(c), d=q(d), cost=cost, status="ok")
    out = {}
    for cls in ("F", "E"):
        V, w, opt = solve(I, cls)
        cert = certify(I, S, w, cls)
        if cert is None or len(opt) != 1:
            rec["status"] = "inconclusive"
            rec[f"{cls}_failure"] = "certificate failed" if cert is None else "multiple optimal candidates"
        out[cls] = (V, w, cert)
    VN = objective(I, S, mu_at(n, I.lam, I.alpha), list(I.w0))
    for cls, (V, w, cert) in out.items():
        v = [w[i] - I.w0[i] for i in range(I.d)]
        rec[cls] = dict(value=q(V), holdings=[q(x) for x in w], trades=[q(x) for x in v],
                        cost=q(sum(I.kbuy[i] * max(v[i], 0) + I.ksell[i] * max(-v[i], 0) for i in range(I.d))),
                        cash=q(cash(I, w)), eta=None if cert is None else [q(cert[0]), q(cert[1])],
                        at_upper=[w[i] == I.wbar[i] for i in range(I.d)], at_zero=[w[i] == 0 for i in range(I.d)])
    rec["N_value"] = q(VN)
    VF, wF, _ = out["F"]
    VE, wE, certE = out["E"]
    rec["active_trade"] = q(wF[0] - a0)
    rec["abs_active_trade"] = q(abs(wF[0] - a0))
    rec["VF_minus_VE"] = q(VF - VE)
    rec["VE_minus_VN"] = q(VE - VN)
    cl = claim009(I, S, wE)
    rec["claim009"] = dict(alpha_c=q(cl["alpha_c"]), I=[q(cl["lo"]), q(cl["hi"])], L=q(cl["L"]), U=q(cl["U"]),
                           C=[q(cl["C"][0]), q(cl["C"][1])], kE=q(cl["kE"]),
                           width_terms=None if cl["width_terms"] is None else [q(t) for t in cl["width_terms"]])
    # agreement checks: claim-009 I equals the E certificate's multiplier set; C predicts F's no-trade at x = alpha_bar
    rec["I_matches_certificate"] = certE is not None and (cl["lo"], cl["hi"]) == certE
    lo_c, hi_c = cl["C"]
    x0 = ALPHA_BAR
    inC = (lo_c == "-inf" or lo_c <= x0) and (hi_c in ("inf", INF) or x0 <= hi_c)
    rec["C_predicts_no_trade"] = inC
    rec["C_prediction_matches_F"] = inC == (wF[0] == a0)
    # J and the admissible band
    rec["J_lower_open"] = q(amin)
    adm_lo = amin if lo_c == "-inf" or lo_c <= amin else lo_c
    rec["C_cap_J"] = dict(lower=q(adm_lo), lower_open=(lo_c == "-inf" or lo_c <= amin), upper=q(hi_c),
                          empty=(hi_c not in ("inf", INF) and hi_c <= amin))
    # probes
    probes = []
    for name, e, side in (("L", lo_c, "lower"), ("U", hi_c, "upper")):
        if e in ("-inf", "inf", INF):
            continue
        for tag, x in (("endpoint", e), ("minus", e - DELTA), ("plus", e + DELTA)):
            p = dict(edge=name, point=tag, x=q(x))
            if not (x > amin) or not positive_everywhere(n, x - ALPHA_BAR):
                p["result"] = "inadmissible (x not in J)"
                probes.append(p)
                continue
            Ix = replace(I, alpha=x)
            Vx, wx, optx = solve(Ix, "F")
            cx = certify(Ix, S, wx, "F")
            inside = (lo_c == "-inf" or lo_c <= x) and (hi_c in ("inf", INF) or x <= hi_c)
            p["a_star"] = q(wx[0])
            p["certified"] = cx is not None and len(optx) == 1
            p["expected_no_trade"] = inside
            p["agrees"] = p["certified"] and (inside == (wx[0] == a0))
            probes.append(p)
    rec["probes"] = probes
    rec["state_key"] = [q(x) for x in I.w0] + [q(I.k0)] + [q(x) for x in I.wbar] + [cost, n]
    return rec


# ---------------------------------------------------------------- targets
def targets(rows):
    by = {(r["menu"], r["a0"], r["c"], r["d"], r["cost"]): r for r in rows}
    fr = lambda s: Fr(s)  # noqa: E731
    ok = lambda r: r["status"] == "ok"  # noqa: E731
    found = {"H1": [], "H2": [], "H3": []}
    incon = {"H1": 0, "H2": 0, "H3": 0}
    for n, a0, c, cost in product(MENUS, A0S, CS, [k[0] for k in COSTS]):
        for d_lo, d_hi in zip(DS, DS[1:]):           # H1: tightening caps (d_hi -> d_lo) weakly increases |trade|
            r_t, r_l = by[(n, q(a0), q(c), q(d_lo), cost)], by[(n, q(a0), q(c), q(d_hi), cost)]
            if not (ok(r_t) and ok(r_l)):
                incon["H1"] += 1
                continue
            if fr(r_t["abs_active_trade"]) < fr(r_l["abs_active_trade"]):
                found["H1"].append((r_l, r_t))
    for n, a0, cost in product(MENUS, A0S, [k[0] for k in COSTS]):
        for c_lo, c_hi in zip(CS, CS[1:]):           # H2 at d = 1: more initial cash weakly decreases |trade|
            r_a, r_b = by[(n, q(a0), q(c_lo), q(Fr(1)), cost)], by[(n, q(a0), q(c_hi), q(Fr(1)), cost)]
            if not (ok(r_a) and ok(r_b)):
                incon["H2"] += 1
                continue
            if fr(r_b["abs_active_trade"]) > fr(r_a["abs_active_trade"]):
                found["H2"].append((r_a, r_b))
    sym = ["Zero", "Equal low", "Equal medium", "Equal high"]
    for n, c, d in product(MENUS, CS, DS):            # H3 at a0 = 1/2: higher common rate weakly widens the band
        for k1, k2 in zip(sym, sym[1:]):
            r1, r2 = by[(n, q(Fr(1, 2)), q(c), q(d), k1)], by[(n, q(Fr(1, 2)), q(c), q(d), k2)]
            if not (ok(r1) and ok(r2)) or r1["claim009"]["width_terms"] is None or r2["claim009"]["width_terms"] is None:
                incon["H3"] += 1
                continue
            w1 = sum(fr(t) for t in r1["claim009"]["width_terms"])
            w2 = sum(fr(t) for t in r2["claim009"]["width_terms"])
            if w2 < w1:
                found["H3"].append((r1, r2))
    key = lambda pr: (pr[0]["menu"], fr(pr[0]["a0"]), fr(pr[0]["c"]), fr(pr[0]["d"]), COST_ORDER[pr[0]["cost"]])  # noqa: E731
    for h in found:
        found[h].sort(key=key)
    return found, incon


def main() -> None:
    t0 = time.time()
    checks = {}
    S = {n: sigma_scen(n) for n in MENUS}
    for n in MENUS:
        checks[f"menu{n}_Sigma_positive_definite"] = pos_def(S[n])
        checks[f"menu{n}_positive_at_every_support_point"] = positive_everywhere(n)
        checks[f"menu{n}_Sigma_equals_formula"] = S[n] == [[Fr(x) for x in r] for r in
                                                          __import__("m2").sigma_formula(instance(n, Fr(0), Fr(0), Fr(0), "Zero"))]
    checks["shared_instruments_same_law"] = all(S[1][i][j] == S[2][i][j] for i in range(2) for j in range(2))
    checks["belief_mean"] = [q(LAM_BAR[0]), q(LAM_BAR[1]), q(ALPHA_BAR)]
    amin = {n: alpha_min(n) for n in MENUS}
    rows = [row(n, a0, c, d, cost, S[n], amin[n])
            for n, a0, c, d, (cost, _, _) in product(MENUS, A0S, CS, DS, COSTS)]
    found, incon = targets(rows)
    (HERE / "results.json").write_text(json.dumps(dict(checks=checks, alpha_min={str(k): q(v) for k, v in amin.items()},
                                                       rows=rows), indent=1))
    ce = {h: [dict(first=[p[0][k] for k in ("menu", "a0", "c", "d", "cost")],
                   second=[p[1][k] for k in ("menu", "a0", "c", "d", "cost")],
                   abs_trade=[p[0]["abs_active_trade"], p[1]["abs_active_trade"]],
                   width=[None if p[i]["claim009"]["width_terms"] is None else
                          q(sum(Fr(t) for t in p[i]["claim009"]["width_terms"])) for i in (0, 1)],
                   F_holdings=[p[0]["F"]["holdings"], p[1]["F"]["holdings"]])
              for p in v] for h, v in found.items()}
    (HERE / "counterexamples.json").write_text(json.dumps(dict(counterexamples=ce, inconclusive_pairs=incon), indent=1))
    summarize(rows, checks, amin, found, incon)
    print(f"\nseconds: {time.time() - t0:.0f}")


def summarize(rows, checks, amin, found, incon):
    fr = Fr
    print("### Validation\n")
    for k, v in checks.items():
        print(f"- {k}: {v}")
    print(f"- J lower endpoints (open): menu 1 {float(amin[1]):.6f}, menu 2 {float(amin[2]):.6f}")
    nr = len(rows)
    distinct = len({json.dumps(r["state_key"]) for r in rows})
    inc = [r for r in rows if r["status"] != "ok"]
    probes = [p for r in rows for p in r["probes"]]
    adm = [p for p in probes if "a_star" in p]
    print(f"- raw rows {nr}; distinct states {distinct}; inconclusive rows {len(inc)}")
    print(f"- claim 009 I equals the E certificate's multiplier set: {sum(r['I_matches_certificate'] for r in rows)}/{nr}")
    print(f"- claim 009 C predicts F's no-active-trade decision at alpha_bar: {sum(r['C_prediction_matches_F'] for r in rows)}/{nr}")
    print(f"- boundary probes: {len(probes)} total, {len(adm)} admissible, {sum(p['certified'] for p in adm)} certified, "
          f"{sum(p['agrees'] for p in adm)} agree with C, {len(probes) - len(adm)} inadmissible (outside J)")
    print("\n### Targets (exact, no tolerance)\n")
    print("| Target | Violations | Pairs skipped as inconclusive or width undefined |\n|---|---|---|")
    for h in ("H1", "H2", "H3"):
        print(f"| {h} | {len(found[h])} | {incon[h]} |")
    for h in ("H1", "H2", "H3"):
        if found[h]:
            a, b = found[h][0]
            print(f"\n**{h} first witness** (menu, a0, c, d, cost): {[a[k] for k in ('menu', 'a0', 'c', 'd', 'cost')]} vs "
                  f"{[b[k] for k in ('menu', 'a0', 'c', 'd', 'cost')]}")
            for r in (a, b):
                wt = r["claim009"]["width_terms"]
                print(f"- d={r['d']}, c={r['c']}: F holdings {r['F']['holdings']}, cash {r['F']['cash']}, "
                      f"|trade| {r['abs_active_trade']}, E holdings {r['E']['holdings']}, I {r['claim009']['I']}, "
                      f"C {r['claim009']['C']}, width {None if wt is None else q(sum(Fr(t) for t in wt))}, "
                      f"F at upper {r['F']['at_upper']}")
    print("\n### Primary panel a0 = 1/2: band width and its three terms (bp), by menu and cost, median over c and d\n")
    print("| Menu | Cost | Rows | Width | kappa+_A(1+hi) | kappa-_A(1+lo) | hi-lo | Rows with active trade at alpha_bar |")
    print("|---|---|---|---|---|---|---|---|")
    for n, (cost, _, _) in product(MENUS, COSTS):
        rs = [r for r in rows if r["menu"] == n and r["a0"] == "1/2" and r["cost"] == cost and r["status"] == "ok"
              and r["claim009"]["width_terms"] is not None]
        if not rs:
            continue
        def med(vals):
            s = sorted(vals)
            m = len(s)
            return s[m // 2] if m % 2 else (s[m // 2 - 1] + s[m // 2]) / 2
        wt = [[fr(t) for t in r["claim009"]["width_terms"]] for r in rs]
        print(f"| {n} | {cost} | {len(rs)} | {float(med([sum(x) for x in wt])) * 1e4:.3f} | "
              f"{float(med([x[0] for x in wt])) * 1e4:.3f} | {float(med([x[1] for x in wt])) * 1e4:.3f} | "
              f"{float(med([x[2] for x in wt])) * 1e4:.3f} | {sum(fr(r['active_trade']) != 0 for r in rs)} |")
    print("\n### Cash sweep at d = 1 (separate from the crossed table): |active trade| by c, a0 = 1/2\n")
    print("| Menu | Cost | " + " | ".join(f"c={q(c)}" for c in CS) + " |\n|---|---|" + "---|" * len(CS))
    for n, (cost, _, _) in product(MENUS, COSTS):
        vals = []
        for c in CS:
            r = next(r for r in rows if r["menu"] == n and r["a0"] == "1/2" and r["c"] == q(c) and r["d"] == "1/1"
                     and r["cost"] == cost)
            vals.append("inconcl." if r["status"] != "ok" else f"{float(fr(r['abs_active_trade'])):.4f}")
        print(f"| {n} | {cost} | " + " | ".join(vals) + " |")
    print("\n### Cap sweep: |active trade| by d, a0 = 1/2, c = 1/2\n")
    print("| Menu | Cost | " + " | ".join(f"d={q(d)}" for d in DS) + " |\n|---|---|" + "---|" * len(DS))
    for n, (cost, _, _) in product(MENUS, COSTS):
        vals = []
        for d in DS:
            r = next(r for r in rows if r["menu"] == n and r["a0"] == "1/2" and r["c"] == "1/2" and r["d"] == q(d)
                     and r["cost"] == cost)
            vals.append("inconcl." if r["status"] != "ok" else f"{float(fr(r['abs_active_trade'])):.4f}")
        print(f"| {n} | {cost} | " + " | ".join(vals) + " |")


if __name__ == "__main__":
    main()
