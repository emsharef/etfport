"""Red's reproduction of experiment 010, written from the registered Design without reading run.py.

It reuses red's own exact engine from experiments/009/red_reproduce.py. That engine provides the
maximizers over F and E by piece and line enumeration, exact nonemptiness of C_N, the vertex
certificates and the finite quantile. The fixture constants are replaced by the Design's: incumbent
(3/10, 3/10, 2/5), gamma = 400, Theta_4 = [1/100, 1/50] x [0, 1/50] x [-1/100, 1/100] and
lambda_* = (1/80, 1/100). Shocks stay as in experiment 009, all scaled by 1/10, the ETF residual included.
Domains: (a) alpha uncertain, Theta_4; (b) alpha known, the alpha interval replaced by {alpha_*}.
Exact rational arithmetic over every count vector.

Usage: uv run python experiments/010/red_reproduce.py
"""
import itertools
import sys
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "009"))
import red_reproduce as R  # noqa: E402  (red's experiment 009 engine)

M4 = R.M4
# Fixture constants of experiment 010 (the engine reads these module globals).
for mod in (M4, R):
    mod.AM, mod.PM, mod.KM, mod.GAMMA = F(3, 10), F(3, 10), F(2, 5), F(400)
THETA4 = ((F(1, 100), F(1, 50)), (F(0), F(1, 50)), (F(-1, 100), F(1, 100)))
R.LAM = (F(1, 80), F(1, 100))
NULLS = [F(-49, 10000), F(-29, 10000), F(-1, 1000)]
ALTS = [F(-1, 125), F(1, 500), F(3, 500)]


def cells(al, domain):
    R.BOX = M4.BOX = domain
    th_s = R.LAM + (al,)
    oracleE = R.argmax_E(th_s)
    supE_s = R.Qy(oracleE, th_s)
    G = R.Qy(R.argmax_F(th_s), th_s) - supE_s
    out = []
    for N in (2, 4, 6, 8):
        hist = []
        for m, ef in R.law_f(N):
            th_h = tuple(th_s[i] + ef[i] for i in range(3))
            T = N * sum(ef[i] * R.OMI[i][j] * ef[j] for i in range(3) for j in range(3))
            hist.append((m, th_h, T, R.argmax_F(th_h), R.argmax_E(th_h), N * R.min_mahal_box(th_h)))
        for eta in (F(1, 20), F(1, 4)):
            Tl = defaultdict(F)
            for m, _, T, *_x in hist:
                Tl[T] += m
            acc = F(0)
            for v in sorted(Tl):
                acc += Tl[v]
                if acc >= 1 - eta:
                    t = v
                    break
            r = [M4.ub_sqrt(t * R.fr(R.OM[i, i]) / N) for i in range(3)]
            acc_ = {k: defaultdict(F) for k in ("valid", "weak", "plugin")}
            for m, th_h, T, wF, vE, mm in hist:
                empty = mm > t
                active = wF[0] != R.AM
                box = [(max(domain[i][0], th_h[i] - r[i]), min(domain[i][1], th_h[i] + r[i])) for i in range(3)]
                verts = list(itertools.product(*box)) if all(lo <= hi for lo, hi in box) else []
                dec = {}
                if empty or not active or not verts:
                    dec["valid"] = dec["weak"] = False
                else:
                    dec["valid"] = min(R.Qy(wF, v) - R.supE(v) for v in verts) > 0
                    dec["weak"] = min(R.Qy(wF, v) - R.Qy(vE, v) for v in verts) > 0
                dec["plugin"] = active and R.Qy(wF, th_h) - R.supE(th_h) > 0
                # counted only when C_N itself is nonempty (the certification box can be nonempty
                # while the pinned-alpha slice of C_N is empty); this reading matches the reported column
                varies = (not empty) and len({R.argmax_E(v) for v in verts}) > 1 if verts else False
                for k, cert in dec.items():
                    a = acc_[k]
                    wimp = wF if cert else vE
                    a["cov"] += m * (T <= t); a["emp"] += m * empty
                    a["vdiff"] += m * (vE != oracleE); a["varies"] += m * varies
                    a["wdiff"] += m * (dec["weak"] != dec["valid"])
                    a["pc"] += m * cert; a["pf"] += m * (cert and R.Qy(wF, th_s) - supE_s <= 0)
                    a["eadv"] += m * (R.Qy(wimp, th_s) - supE_s)
                    a["miss"] += m * (not cert) * G
                    a["short"] += m * (not cert) * (supE_s - R.Qy(vE, th_s))
            for k in ("valid", "weak", "plugin"):
                out.append(dict(rule=k, eta=eta, alpha=al, N=N, G=G, **acc_[k]))
    return out


def main():
    fails, rows = [], []
    for al in NULLS + ALTS:
        for name, dom in (("alpha uncertain", THETA4), ("alpha known", THETA4[:2] + ((al, al),))):
            for c in cells(al, dom):
                c["domain"] = name
                rows.append(c)
    # Compare with every row of the reported table.
    rep = {}
    for line in open(HERE.parent / "010-m4-moving-comparator.md"):
        c = [x.strip() for x in line.split("|")]
        if len(c) == 18 and c[2] in ("valid", "weak", "plugin"):
            rep[(c[1], c[2], c[3], c[4], c[6])] = [float(c[5])] + [float(x) for x in c[7:17]]
    keys = ("cov", "emp", "vdiff", "varies", "wdiff", "pc", "pf", "eadv", "miss", "short")
    worst, matched, where = 0.0, 0, None
    global BAD
    BAD = []
    for r in rows:
        key = (r["domain"], r["rule"], str(r["eta"]), str(r["alpha"]), str(r["N"]))
        if key not in rep:
            continue
        matched += 1
        mine = [float(r["G"]) * 1e4] + [float(r[k]) for k in keys[:7]] + [float(r[k]) * 1e4 for k in keys[7:]]
        rp = rep[key]
        tol = [5e-4] + [5e-5] * 7 + [5e-4] * 3
        devs = [abs(a - b) / t for a, b, t in zip(mine, rp, tol)]
        dev = max(devs)
        if dev > 1.0 + 1e-6:          # exact ties such as 0.03125 print as 0.0312
            names = ["G", "cov", "emp", "vdiff", "varies", "wdiff", "pc", "pf", "eadv", "miss", "short"]
            BAD.append((key, [(n, round(a, 4), round(b, 4)) for n, a, b, d_ in zip(names, mine, rp, devs) if d_ > 1.0]))
        if dev > worst:
            worst, where = dev, key
    print(f"rows {len(rows)}; matched to the reported table {matched}; largest deviation in units of the last "
          f"printed digit {worst:.2f} at {where}")
    print(f"cells beyond rounding: {len(BAD)}")
    for b in BAD:
        print("  ", b)
    if matched != len(rows) or worst > 1.0 + 1e-6:
        fails.append("does not match the reported table")
    for rule in ("valid", "weak", "plugin"):
        rs = [r for r in rows if r["rule"] == rule]
        over = [(r["domain"], str(r["alpha"]), r["N"], str(r["eta"]), round(float(r["pf"]), 4)) for r in rs if r["pf"] > r["eta"]]
        print(f"{rule}: cells with P(false cert) > eta: {len(over)} of {len(rs)}; coverage < 1 - eta: "
              f"{sum(r['cov'] < 1 - r['eta'] for r in rs)}; max P(false cert) {max(float(r['pf']) for r in rs):.4f}")
        if rule == "weak":
            print("  weak exceedances:", over)
    # Diagnostic for the reported eta non-monotonicity (alpha known, alpha_* = 3/500, N = 8).
    for r in rows:
        if r["domain"] == "alpha known" and r["alpha"] == F(3, 500) and r["N"] == 8 and r["rule"] == "valid":
            print(f"alpha known, alpha_*=3/500, N=8, eta={r['eta']}: P(certify) {float(r['pc']):.4f}, P(empty C_N) "
                  f"{float(r['emp']):.4f}, coverage {float(r['cov']):.4f}")
    print(f"\nFailures: {len(fails)}")
    for f in fails:
        print(" -", f)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
