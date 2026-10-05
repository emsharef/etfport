"""Red's reproduction of experiment 009, written from the registered Design without reading run.py.

Exact rational arithmetic over every count vector, as the Design prescribes; there is no sampling.

Part X (claim 014's laws; the M4 gate depends on alpha_hat alone): the gate's power at theta_+, the
largest false certification over the alpha grid, coverage and P(empty C_N), for N_obs = 1..10 and
eta in {1/16, 1/4}. Claim 014's benchmark is checked at N = 1, 2, 3 by an exact endpoint
likelihood-ratio (Neyman-Pearson) computation on the full public records.

Part Y (red's M4 fixture from checks/red-m4-definition/check.py, whose primitives are imported):
- exact global maximizers of Q over F and E, by red's own sign-piece and active-line enumeration;
- exact nonemptiness of C_N, by a box-constrained quadratic minimum over the 27 active sets;
- the three registered rules and metrics, for the registered grid and Deviation 1's band cells.

Usage: uv run python experiments/009/red_reproduce.py
"""
import itertools
import json
import sys
from collections import defaultdict
from fractions import Fraction as F
from math import comb
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent / "checks" / "red-m4-definition"))
import check as M4  # noqa: E402  (red's own fixture: shocks, Omega, law, quantile, Q, supE, box)


def fr(x):
    x = sp.Rational(x)
    return F(int(x.p), int(x.q))


# ------------------------------------------------------------------ Part X: claim 014's laws
H = F(1, 10)
BE14 = F(13, 1600)


def Q14(w, al):
    a, p = w
    return a * al + p / 80 - a * a / 200 - p * p / 80


def plugin14(al):
    c = [(F(0), F(0)), (F(1), F(0)), (F(0), F(1)), (F(0), F(1, 2))]
    a = 100 * al
    if 0 <= a <= F(1, 2):
        c.append((a, F(1, 2)))
    if 0 <= a <= 1:
        c.append((a, F(0)))
    a = (al - F(1, 80) + F(1, 40)) / (F(1, 100) + F(1, 40))
    if 0 <= a <= 1:
        c.append((a, 1 - a))
    best = max(Q14(w, al) for w in c)
    return min(w for w in c if Q14(w, al) == best)


def adv14(w, al):
    return Q14(w, al) - F(1, 320)


def gate14(ah, t, N):
    """(certify, empty) for M4's gate: C_N = [ah -+ H sqrt(t/N)] intersect [-H, H]."""
    r2 = H * H * t / N

    def gt(x):                       # x > sqrt(r2)
        return x > 0 and x * x > r2
    if gt(ah - H) or gt(-H - ah):
        return False, True
    w = plugin14(ah)
    if w[0] == 0:
        return False, False
    if not gt(ah + H):               # lower end of C_N is -H
        return adv14(w, -H) > 0, False
    astar = (F(1, 320) + w[0] ** 2 / 200 + w[1] ** 2 / 80 - w[1] / 80) / w[0]   # Adv(w; astar) = 0
    return gt(ah - astar), False


def part_x():
    out, fails = [], []
    grid = [-H, -H / 2, F(0), BE14, F(1, 40), H]
    for eta in (F(1, 16), F(1, 4)):
        for N in range(1, 11):
            law = [(F(comb(N, k), 2 ** N), F(2 * k - N, N) * H) for k in range(N + 1)]   # (mass, e)
            T = defaultdict(F)
            for m, e in law:
                T[N * e * e / (H * H)] += m
            acc = F(0)
            for v in sorted(T):
                acc += T[v]
                if acc >= 1 - eta:
                    t = v
                    break
            cov = sum(m for v, m in T.items() if v <= t)
            power = empty = F(0)
            worst = F(0)
            for al in grid:
                fc = F(0)
                for m, e in law:
                    c, em = gate14(al + e, t, N)
                    if al == H:
                        power += m * c
                        empty += m * em
                    if c and adv14(plugin14(al + e), al) <= 0:
                        fc += m
                worst = max(worst, fc)
            bI = min(F(1), 1 - F(1, 2 ** N) + eta)
            out.append((eta, N, power, bI, worst, cov, empty))
            if worst > eta or cov < 1 - eta:
                fails.append(f"Part X validity fails at eta={eta}, N={N}")
    return out, fails


def np_benchmark(law, N, eta):
    """Exact endpoint Neyman-Pearson power at theta_+ subject to P_-(certify) <= eta (full records)."""
    def rec(al):
        d = defaultdict(F)
        for s, t_, u in itertools.product((-1, 1), repeat=3):
            zE = F(t_ * (3 - u), 20) if law == "I" else F(t_ * (3 - s), 20)
            d[(al + F(s, 10), F(1, 80) + zE)] += F(1, 8)
        return d

    def hist(al):
        one = rec(al)
        h = defaultdict(F)
        for rs in itertools.product(one.items(), repeat=N):
            m = F(1)
            for _, q in rs:
                m *= q
            h[tuple(r for r, _ in rs)] += m
        return h
    P, Qp = hist(-H), hist(H)
    keys = set(P) | set(Qp)
    order = sorted(keys, key=lambda k: -(Qp.get(k, 0) / P[k]) if P.get(k, 0) else -10 ** 9)
    budget, pw = eta, F(0)
    for k in order:
        pm, pp = P.get(k, F(0)), Qp.get(k, F(0))
        if pm == 0:
            pw += pp
            continue
        take = min(F(1), budget / pm)
        pw += take * pp
        budget -= take * pm
    return pw


# ------------------------------------------------------------------ Part Y: red's M4 fixture
# The Design says "8 equiprobable sign scenarios scaled by 1/10". Red's check file scales the factor and
# active shocks but not the ETF residual (1/200); the experiment scales all of them, as the Design's words
# say, so the ETF residual is 1/2000 here. This changes Sigma only, not Omega (see red's Review).
SH = [(q, zf, zA, (zE[0] / 10,)) for q, zf, zA, zE in M4.shocks("nonsingular", F(1, 10))]
S = M4.sigma(SH)
OM = M4.omega(SH)
OMI = [[fr(x) for x in row] for row in OM.inv().tolist()]
AM, PM, KM, KA, KE, GAMMA = M4.AM, M4.PM, M4.KM, M4.KA, M4.KE, M4.GAMMA
BOX = M4.BOX
LAM = (F(1, 50), F(1, 100))


def Qy(w, th):
    return M4.Q(w, th, S)


def cash(w):
    a, p = w
    return KM - (a - AM) - (p - PM) - KA * abs(a - AM) - KE * abs(p - PM)


def feasible_F(w):
    return 0 <= w[0] <= 1 and 0 <= w[1] <= 1 and cash(w) >= 0


def argmax_F(th):
    """Exact global maximizer of Q(.; th) over F (lexicographically smallest on ties).

    Q is concave and piecewise quadratic, with pieces fixed by the trade signs. On each piece the
    maximum over its polygon lies at an interior stationary point, at a stationary point along one
    boundary line, or at the intersection of two lines. The lines are the bounds, the piece lines
    a = a^-, p = p^- and the piece's cash line. All such points are enumerated and every feasible
    one is evaluated with the true Q.
    """
    lam, al = th[:2], th[2]
    g = (M4.BA[0] * lam[0] + M4.BA[1] * lam[1] + al, M4.BE[0] * lam[0] + M4.BE[1] * lam[1])
    Hm = [[GAMMA * S[i][j] for j in range(2)] for i in range(2)]          # -Hessian
    cands = set()
    for sa, sp_ in itertools.product((-1, 1), repeat=2):
        lin = (g[0] - sa * KA, g[1] - sp_ * KE)                            # gradient = lin - Hm w
        det = Hm[0][0] * Hm[1][1] - Hm[0][1] * Hm[1][0]
        if det != 0:
            cands.add(((lin[0] * Hm[1][1] - lin[1] * Hm[0][1]) / det, (Hm[0][0] * lin[1] - Hm[1][0] * lin[0]) / det))
        # lines as (c_a, c_p, r): c_a a + c_p p = r
        lines = [(F(1), F(0), v) for v in (F(0), F(1), AM)] + [(F(0), F(1), v) for v in (F(0), F(1), PM)]
        ca, cp = 1 + sa * KA, 1 + sp_ * KE
        lines.append((ca, cp, KM + ca * AM + cp * PM))                     # cash = 0 on this piece
        for (a1, b1, r1) in lines:                                         # stationary along one line
            if b1 != 0:        # p = (r1 - a1 a)/b1, direction (1, -a1/b1)
                d = (F(1), -a1 / b1); w0 = (F(0), r1 / b1)
            else:
                d = (F(0), F(1)); w0 = (r1 / a1, F(0))
            curv = sum(d[i] * Hm[i][j] * d[j] for i in range(2) for j in range(2))
            slope0 = sum(d[i] * (lin[i] - sum(Hm[i][j] * w0[j] for j in range(2))) for i in range(2))
            if curv != 0:
                s = slope0 / curv
                cands.add((w0[0] + s * d[0], w0[1] + s * d[1]))
        for (a1, b1, r1), (a2, b2, r2) in itertools.combinations(lines, 2):
            det2 = a1 * b2 - a2 * b1
            if det2 != 0:
                cands.add(((r1 * b2 - r2 * b1) / det2, (a1 * r2 - a2 * r1) / det2))
    feas = [w for w in cands if feasible_F(w)]
    best = max(Qy(w, th) for w in feas)
    return min(w for w in feas if Qy(w, th) == best)


def argmax_E(th):
    hi = PM + KM / (1 + KE)
    cands = {F(0), PM, min(hi, F(1))}
    lam = th[:2]
    lin = M4.BE[0] * lam[0] + M4.BE[1] * lam[1] - GAMMA * AM * S[0][1]
    for sgn, lo_, hi_ in ((-1, F(0), PM), (1, PM, min(hi, F(1)))):
        p = (lin - sgn * KE) / (GAMMA * S[1][1])
        if lo_ <= p <= hi_:
            cands.add(p)
    best = max(Qy((AM, p), th) for p in cands)
    return (AM, min(p for p in cands if Qy((AM, p), th) == best))


def supE(th):
    return Qy(argmax_E(th), th)


def det3(M):
    n = len(M)
    if n == 1:
        return M[0][0]
    if n == 2:
        return M[0][0] * M[1][1] - M[0][1] * M[1][0]
    return sum((-1) ** j * M[0][j] * det3([row[:j] + row[j + 1:] for row in M[1:]]) for j in range(3))


def solve_exact(A, b):
    """Cramer's rule in Fractions (A is a principal block of the positive definite Omega^-1)."""
    d = det3(A)
    return [det3([row[:k] + [b[i]] + row[k + 1:] for i, row in enumerate(A)]) / d for k in range(len(A))]


def min_mahal_box(th_hat):
    """Exact min over theta in BOX of (th_hat - theta)' Omega^-1 (th_hat - theta)."""
    best = None
    for act in itertools.product((None, 0, 1), repeat=3):
        fixed = {i: BOX[i][act[i]] for i in range(3) if act[i] is not None}
        free = [i for i in range(3) if act[i] is None]
        th = [None] * 3
        for i, v in fixed.items():
            th[i] = v
        if free:                     # stationarity in the free coordinates: Omega^-1 (th - th_hat) = 0 there
            A = [[OMI[i][j] for j in free] for i in free]
            b = [sum(OMI[i][j] * th_hat[j] for j in range(3)) - sum(OMI[i][j] * fixed[j] for j in fixed) for i in free]
            sol = solve_exact(A, b)
            for k, i in enumerate(free):
                th[i] = sol[k]
        if all(BOX[i][0] <= th[i] <= BOX[i][1] for i in range(3)):
            d = [th_hat[i] - th[i] for i in range(3)]
            v = sum(d[i] * OMI[i][j] * d[j] for i in range(3) for j in range(3))
            best = v if best is None else min(best, v)
    return best


LAWS = {}


def law_f(N):
    if N not in LAWS:
        LAWS[N] = [(m, [fr(x) for x in e]) for m, e in M4.law(SH, N)]
    return LAWS[N]


def part_y(alphas):
    rows = []
    for al in alphas:
        th_s = LAM + (al,)
        G = Qy(argmax_F(th_s), th_s) - supE(th_s)
        supE_s = supE(th_s)
        for N in (2, 4, 6, 8):
            hist = []
            for m, ef in law_f(N):
                th_h = tuple(th_s[i] + ef[i] for i in range(3))
                T = N * sum(ef[i] * OMI[i][j] * ef[j] for i in range(3) for j in range(3))
                wF, vE = argmax_F(th_h), argmax_E(th_h)
                hist.append((m, ef, th_h, T, wF, vE, N * min_mahal_box(th_h)))
            for eta in (F(1, 20), F(1, 4)):
                Tl = defaultdict(F)
                for m, *_x in hist:
                    Tl[_x[2]] += m
                acc = F(0)
                for v in sorted(Tl):
                    acc += Tl[v]
                    if acc >= 1 - eta:
                        t = v
                        break
                r = [M4.ub_sqrt(t * fr(OM[i, i]) / N) for i in range(3)]
                for rule in ("valid", "weak", "plugin"):
                    cov = emp = pc = pf = eadv = miss = short = F(0)
                    for m, ef, th_h, T, wF, vE, mm in hist:
                        empty = mm > t
                        cov += m * (T <= t)
                        emp += m * empty
                        active = wF[0] != AM
                        if rule == "plugin":
                            cert = active and Qy(wF, th_h) - supE(th_h) > 0
                        elif empty or not active:
                            cert = False
                        else:
                            box = [(max(BOX[i][0], th_h[i] - r[i]), min(BOX[i][1], th_h[i] + r[i])) for i in range(3)]
                            if rule == "valid":
                                ell = min(Qy(wF, v) - supE(v) for v in itertools.product(*box))
                            else:
                                ell = min(Qy(wF, v) - Qy(vE, v) for v in itertools.product(*box))
                            cert = ell > 0
                        wimp = wF if cert else vE
                        a_imp = Qy(wimp, th_s) - supE_s
                        pc += m * cert
                        pf += m * (cert and Qy(wF, th_s) - supE_s <= 0)
                        eadv += m * a_imp
                        miss += m * (not cert) * G
                        short += m * (supE_s - Qy(vE, th_s))
                    rows.append(dict(rule=rule, eta=eta, alpha=al, G=G, N=N, cov=cov, emp=emp, pc=pc, pf=pf,
                                     eadv=eadv, miss=miss, short=short))
    return rows


def main():
    fails = []
    xs, f = part_x()
    fails += f
    print("### Part X (claim 014 laws; the M4 gate is identical in I and R)\n")
    print("| eta | N | gate power at theta_+ | benchmark I | max false cert (alpha grid) | coverage | P(empty) at theta_+ |")
    print("|---|---|---|---|---|---|---|")
    for eta, N, pw, bI, worst, cov, emp in xs:
        print(f"| {eta} | {N} | {float(pw):.4f} | {float(bI):.4f} | {float(worst):.4f} | {float(cov):.4f} | {float(emp):.4f} |")
    ok_np = all(np_benchmark(law, N, eta) == (min(F(1), 1 - F(1, 2 ** N) + eta) if law == "I" else F(1))
                for law in ("I", "R") for N in (1, 2, 3) for eta in (F(1, 16), F(1, 4)))
    print(f"\nEndpoint Neyman-Pearson power equals claim 014's benchmark at N = 1, 2, 3, both laws and eta: {ok_np}")
    if not ok_np:
        fails.append("Part X benchmark mismatch")

    reg = [F(-1, 20), F(-1, 100), F(0), F(1, 100), F(1, 40), F(1, 20), F(1, 10)]
    sup = [F(-3, 400), F(-11, 2000), F(-7, 2000)]
    rows = part_y(reg + sup)
    rep = {}
    for line in open(HERE.parent / "009-m4-certificate-gate.md"):
        c = [x.strip() for x in line.split("|")]
        if len(c) == 14 and c[1] in ("valid", "weak", "plugin"):
            rep[(c[1], c[2], c[3], c[5])] = [float(x) for x in c[6:13]]
    worst = 0.0
    for r in rows:
        mine = [float(r[k]) for k in ("cov", "emp", "pc", "pf")] + [float(r[k]) * 1e4 for k in ("eadv", "miss", "short")]
        key = (r["rule"], str(r["eta"]), str(r["alpha"]), str(r["N"]))
        if key in rep:
            tol = [5e-5] * 4 + [5e-4] * 3                                   # printed rounding
            worst = max(worst, max(abs(a - b) / t for a, b, t in zip(mine, rep[key], tol)))
    print(f"\nPart Y: {len(rows)} rule cells, {len(rep)} reported cells; largest deviation from the printed table, "
          f"in units of its last printed digit: {worst:.2f}")
    if worst > 1.0:
        fails.append("Part Y deviates from the reported tables beyond rounding")
    val = [r for r in rows if r["rule"] == "valid"]
    print(f"valid gate: cells with P(false cert) > eta: {sum(r['pf'] > r['eta'] for r in val)}; coverage < 1 - eta: "
          f"{sum(r['cov'] < 1 - r['eta'] for r in val)}; plug-in cells with P(false cert) > eta: "
          f"{sum(r['pf'] > r['eta'] for r in rows if r['rule'] == 'plugin')} of {len(val)}")
    print(f"weak and valid decisions give identical cell metrics in "
          f"{sum(all(a[k] == b[k] for k in ('pc', 'pf', 'eadv')) for a, b in zip(rows[0::3], rows[1::3]))} of {len(val)} cells; "
          f"max fallback shortfall {max(float(r['short']) for r in rows) * 1e4:.3e} bp")
    print(f"G_* at the registered alphas (bp): {[round(float(r['G']) * 1e4, 3) for r in val if r['N'] == 2 and r['eta'] == F(1, 20)]}")
    print(f"\nFailures: {len(fails)}")
    for x in fails:
        print(" -", x)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
