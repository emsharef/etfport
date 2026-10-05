"""Experiment 028 report (uv run python experiments/028/report.py): each check against its registered tolerance,
by lambda_E, from summary.json."""
import json
from collections import defaultdict
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
LAMES = [1e-6, 1e-8, 1e-10]


def by_lamE(rows, ok, err):
    out = {}
    for le in LAMES:
        rs = [r for r in rows if r["lamE"] == le]
        if rs:
            out[le] = (sum(ok(r) for r in rs), len(rs), max(err(r) for r in rs))
    return out


def show(title, res, unit=""):
    print(f"**{title}**")
    for le, (k, n, e) in res.items():
        print(f"- lambda_E = {le:.0e}: {k}/{n} within tolerance; largest error {e:.3e}{unit}")
    print()


def load():
    S = json.load(open(HERE / "summary.json"))
    for k, v in S.items():
        if isinstance(v, dict) and v and all(isinstance(x, list) for x in v.values()) and k not in ("level_sets", "mc"):
            n = len(next(iter(v.values())))
            S[k] = [{c: v[c][i] for c in v if v[c][i] is not None} for i in range(n)]
    return S


def main():
    S = load()
    # (a) thresholds
    A = S["a"]
    show("(a) buy/sell threshold, |root-found - formula| <= 1e-8 per quarter",
         by_lamE(A, lambda r: abs(r["ref"] - r["formula"]) <= 1e-8, lambda r: abs(r["ref"] - r["formula"])))
    # (c) gaps
    C = S["c"]
    def okg(r, g, f):
        return abs(r[g] - r[f]) <= max(1e-6 * abs(r[f]), 1e-12)
    def relg(r, g, f):
        return abs(r[g] - r[f]) / max(abs(r[f]), 1e-12)
    show("(c) dynamic minus myopic gap, rel 1e-6 or abs 1e-12", by_lamE(C, lambda r: okg(r, "g_dyn", "f_dyn"), lambda r: relg(r, "g_dyn", "f_dyn")), " (relative)")
    show("(c) learning-aware minus static-belief gap, rel 1e-6 or abs 1e-12", by_lamE(C, lambda r: okg(r, "g_learn", "f_learn"), lambda r: relg(r, "g_learn", "f_learn")), " (relative)")
    fails = [r for r in C if r["lamE"] == 1e-10 and not (okg(r, "g_dyn", "f_dyn") and okg(r, "g_learn", "f_learn"))]
    if fails:
        print(f"lambda_E = 1e-10 misses ({len(fails)}), largest absolute differences:")
        for r in sorted(fails, key=lambda r: -max(abs(r['g_dyn'] - r['f_dyn']), abs(r['g_learn'] - r['f_learn'])))[:8]:
            print(f"- N {r['N']} sb {r['sb']} ratio {r['ratio']} lamr {r['lamr']} rho {r['rho']} T {r['T']} cE {r['cE']} x0 {r['x0']} a0 {r['a0']}: "
                  f"dyn {r['g_dyn']:.4e} vs {r['f_dyn']:.4e}; learn {r['g_learn']:.4e} vs {r['f_learn']:.4e}")
        print()
    # T = 1 sanity and signs
    t1 = [r for r in C if r["T"] == 1 and r["lamE"] == 1e-10]
    print(f"T = 1: largest |gap| {max(max(abs(r['g_dyn']), abs(r['g_learn'])) for r in t1):.2e} (both gaps are 0 by definition)\n")
    # scaling of the learning gap in s^2/sigma^2 over the three smallest ratios
    groups = defaultdict(dict)
    for r in C:
        if r["lamE"] == 1e-10 and r["T"] > 1:
            groups[(r["N"], r["sb"], r["lamr"], r["rho"], r["T"], r["cE"], r["x0"], r["a0"])][r["ratio"]] = r
    slopes_ref, slopes_f = [], []
    for g in groups.values():
        xs = np.log([0.01, 0.03, 0.1])
        yr = np.log([g[q]["g_learn"] for q in (0.01, 0.03, 0.1)]); yf = np.log([g[q]["f_learn"] for q in (0.01, 0.03, 0.1)])
        slopes_ref.append(np.polyfit(xs, yr, 1)[0]); slopes_f.append(np.polyfit(xs, yf, 1)[0])
    print(f"**Learning-gap scaling** (slope of log G_learn on log s^2/sigma_A^2 over 0.01-0.1; {len(slopes_ref)} groups, T > 1): "
          f"reference {np.min(slopes_ref):.3f} to {np.max(slopes_ref):.3f} (median {np.median(slopes_ref):.3f}); "
          f"formula {np.min(slopes_f):.3f} to {np.max(slopes_f):.3f}\n")
    # named points
    print("**Named points** (N = 3, s_bar = 0, rho = 1, T = 20, c^E = 0; gaps in bp per quarter = gap / 20 x 1e4):")
    for name, (a0, ratio, lamr) in {"equity-style": (-0.004, 0.03, 10.0), "fixed-income-style": (0.002, 0.3, 1.0)}.items():
        for x0 in (0.0, 0.15):
            r = [r for r in C if r["lamE"] == 1e-10 and r["N"] == 3 and r["sb"] == 0 and r["ratio"] == ratio and r["lamr"] == lamr
                 and r["rho"] == 1.0 and r["T"] == 20 and r["cE"] == 0 and r["x0"] == x0 and r["a0"] == a0][0]
            print(f"- {name} grid neighbour (alpha_hat_0 = {a0 * 100:+.2f}%, s^2/sigma^2 = {ratio}, lambda ratio {lamr}, x0 = {x0}): "
                  f"dynamic {r['g_dyn'] / 20 * 1e4:.3f} bp (formula {r['f_dyn'] / 20 * 1e4:.3f}); learning {r['g_learn'] / 20 * 1e4:.4f} bp (formula {r['f_learn'] / 20 * 1e4:.4f})")
    print()
    # Monte Carlo cross-check
    print("**Monte Carlo cross-check** (20,000 paths; N = 3, s_bar = 0, T = 20, rho = 1, x0 = 0; value units):")
    for name, d in S["mc"].items():
        for k, v in d.items():
            z = (v["mc"] - v["exact"]) / v["se"] if v["se"] > 0 else float("nan")
            print(f"- {name} {k}: exact {v['exact']:.6e}, MC {v['mc']:.6e} (SE {v['se']:.2e}; z = {z:+.2f})")
    print()
    # (d)
    D = S["d"]
    for le in LAMES:
        rs = [r for r in D if r["lamE"] == le]
        sp = [r for r in rs if r["menu"] in ("two-ETF spanning", "phi=0")]
        un = [r for r in rs if r["menu"] not in ("two-ETF spanning", "phi=0")]
        print(f"- (d) lambda_E = {le:.0e}: spanned menus: largest |Jacobian| reference {max(r['ref_max'] for r in sp):.2e}, formula {max(r['form_max'] for r in sp):.2e} "
              f"({sum(r['ref_max'] <= 1e-10 for r in sp)}/{len(sp)} <= 1e-10); unspanned: largest relative difference "
              f"{max(r['diff'] / r['form_max'] for r in un):.2e} ({sum(r['diff'] <= 1e-5 * r['form_max'] for r in un)}/{len(un)} <= 1e-5)")
    for m in ("two-ETF spanning", "phi=0", "phi=15", "phi=45", "phi=90"):
        rs = [r for r in D if r["lamE"] == 1e-10 and r["menu"] == m]
        print(f"  - {m}: ||Pi_U B^A'|| = {rs[0]['unspanned']:.4f}; fund-position sensitivity to the premium mean, largest entry {max(r['form_max'] for r in rs):.3e} (formula), "
              f"{max(r['ref_max'] for r in rs):.3e} (reference); x one prior SD (0.005): {max(r['ref_max'] for r in rs) * 0.005:.4f}")
    print()
    # plug-in
    P = S["plugin"]
    for le in LAMES:
        rs = [r for r in P if r["lamE"] == le and r["T"] > 1 and r["Ceps2"] > 1e-16]
        rat = np.array([r["loss"] / r["Ceps2"] - 1 for r in rs]); eps = np.array([abs(r["eps"]) for r in rs])
        print(f"- plug-in lambda_E = {le:.0e}: |loss/(C eps^2) - 1| at |eps| = 0.01: max {np.abs(rat[eps == 0.01]).max():.3e}; "
              f"0.05: {np.abs(rat[eps == 0.05]).max():.3e}; 0.2: {np.abs(rat[eps == 0.2]).max():.3e}")
    groups = defaultdict(dict)
    for r in P:
        if r["lamE"] == 1e-10 and r["T"] > 1 and r["eps"] > 0 and r["Ceps2"] > 1e-16:
            groups[(r["N"], r["sb"], r["ratio"], r["lamr"], r["rho"], r["T"], r["x0"], r["a0"])][r["eps"]] = abs(r["loss"] / r["Ceps2"] - 1)
    ords = [np.polyfit(np.log([0.01, 0.05, 0.2]), np.log([g[e] for e in (0.01, 0.05, 0.2)]), 1)[0] for g in groups.values() if min(g.values()) > 0]
    print(f"- fitted order of loss/(C eps^2) - 1 in eps (eps > 0; {len(ords)} groups): {np.min(ords):.3f} to {np.max(ords):.3f}, median {np.median(ords):.3f}")
    t1 = [r for r in P if r["T"] == 1 and r["lamE"] == 1e-10 and r["Ceps2"] > 1e-16]
    print(f"- T = 1 rows: |loss/(C eps^2) - 1| at |eps| = 0.01 max {max(abs(r['loss'] / r['Ceps2'] - 1) for r in t1 if abs(r['eps']) == 0.01):.3e}")
    L = S["plugin_limits"]
    lo = [r for r in L if r["lamr"] == 1e-4]
    print(f"- costless limit (lambda ratio 1e-4, eps = 0.01): |loss/myopic - 1| max {max(abs(r['loss'] / r['myopic'] - 1) for r in lo):.3e}, "
          f"|C eps^2/myopic - 1| max {max(abs(r['Ceps2'] / r['myopic'] - 1) for r in lo):.3e}")
    for lr in (1e2, 1e3, 1e4):
        rs = [r for r in L if r["lamr"] == lr and r["lamE"] == 1e-10]
        v = np.array([r["lamA"] * r["Ceps2"] / r["eps"] ** 2 for r in rs]); w = np.array([r["lamA"] * r["loss"] / r["eps"] ** 2 for r in rs])
        print(f"- lambda ratio {lr:.0e}: lambda_A C, median {np.median(v):.4e} (formula), lambda_A loss/eps^2 median {np.median(w):.4e} (reference); "
              f"max |ref/formula - 1| {np.max(np.abs(w / v - 1)):.3e}")
    key = defaultdict(dict)
    for r in L:
        if r["lamE"] == 1e-10 and r["lamr"] >= 1e2:
            key[(r["N"], r["sb"], r["ratio"], r["rho"], r["T"], r["a0"])][r["lamr"]] = r["lamA"] * r["Ceps2"]
    rel = [abs(g[1e4] / g[1e3] - 1) for g in key.values()]
    print(f"- lambda_A C change from ratio 1e3 to 1e4: median {np.median(rel):.2e}, max {np.max(rel):.2e}\n")
    # factor covariance
    F = S["factor_cov"]
    for le in LAMES:
        sp = [r for r in F if r["lamE"] == le and r["menu"] == "two-ETF spanning"]; un = [r for r in F if r["lamE"] == le and r["menu"] == "phi=45"]
        print(f"- factor-covariance error, lambda_E = {le:.0e}: spanning, largest fund-coefficient change {max(r['change'] for r in sp):.2e} "
              f"({sum(r['change'] <= 1e-10 for r in sp)}/{len(sp)} <= 1e-10); phi = 45: smallest change {min(r['change'] for r in un):.2e}, largest {max(r['change'] for r in un):.2e}")
    print()
    # level sets
    for name, L in S["level_sets"].items():
        print(f"- level sets {name}: reference 1 bp crossings (lambda ratio, s^2/sigma^2): dynamic {L['cross']['myopic']}; learning {L['cross']['static']}")
        for k in ("myopic", "static"):
            g = np.array(L["grid"][k]); print(f"  formula gap per quarter on the grid ({k}): max {g.max() * 1e4:.3f} bp, min {g.min() * 1e4:.2e} bp")
    # largest absolute gap differences at the smallest lambda_E, and their convergence
    by = defaultdict(dict)
    for r in C:
        by[(r["N"], r["sb"], r["ratio"], r["lamr"], r["rho"], r["T"], r["cE"], r["x0"], r["a0"])][r["lamE"]] = r
    worst_abs = max(max(abs(d[1e-10][g] - d[1e-10][f]) for g, f in (("g_dyn", "f_dyn"), ("g_learn", "f_learn"))) for d in by.values())
    shrink = min(abs(d[1e-8][g] - d[1e-8][f]) / abs(d[1e-10][g] - d[1e-10][f]) for d in by.values() for g, f in (("g_dyn", "f_dyn"), ("g_learn", "f_learn"))
                 if abs(d[1e-10][g] - d[1e-10][f]) > max(1e-6 * abs(d[1e-10][f]), 1e-12))
    print(f"\n(c) at lambda_E = 1e-10: largest absolute difference {worst_abs:.2e}; every miss shrinks by at least {shrink:.1f}x from lambda_E = 1e-8")
    supplementary()
    print(f"\nseconds: {S['seconds']:.0f}")


def supplementary():
    """Deviation 3: formula-side diagnostics of two registered checks, and the formula at the reference crossings."""
    import importlib.util
    spec = importlib.util.spec_from_file_location("run028", HERE / "run.py"); r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
    print("\n**Supplementary (Deviation 3; formula side, whose identity matched the reference on the grid)**")
    rat = np.array([1e-5, 1e-4, 1e-3, 1e-2]); res = []
    for (N, sb) in r.CONFIGS:
        for lamr in r.LAMR:
            for rho in r.RHOS:
                for T in (4, 20):
                    for x0 in r.X0S:
                        for a0 in r.A0S:
                            g = [r.gap_formula("static", N, sb, q, lamr, rho, T, x0, a0, 0.0) for q in rat]
                            res.append(np.diff(np.log(g)) / np.diff(np.log(rat)))
    res = np.array(res)
    for i in range(3):
        print(f"- learning-gap slope over s^2/sigma^2 in [{rat[i]:.0e}, {rat[i + 1]:.0e}]: {res[:, i].min():.3f} to {res[:, i].max():.3f} (median {np.median(res[:, i]):.3f}; {len(res)} groups)")
    out = []
    for (N, sb) in r.CONFIGS:
        for ratio in r.RATIOS:
            for rho in r.RHOS:
                for T in (4, 20):
                    for a0 in r.A0S:
                        out.append([lr * r.GAMMA * r.SIGA ** 2 * r.plugin_C(N, sb, ratio, lr, rho, T, 0.15, a0) for lr in (1e3, 1e4, 1e5, 1e6, 1e7)])
    out = np.array(out)
    for i, lr in enumerate((1e3, 1e4, 1e5, 1e6)):
        ch = np.abs(out[:, i + 1] / out[:, i] - 1)
        print(f"- lambda_A C, relative change from lambda ratio {lr:.0e} to {lr * 10:.0e}: median {np.median(ch):.2e}, max {ch.max():.2e}")
    S = load()
    errs = []
    for name, L in S["level_sets"].items():
        for k in ("myopic", "static"):
            for l, q in L["cross"][k]:
                errs.append(abs(r.gap_formula(k, 1, 0.0, q, l, 1.0, 20, 0.0, r.NAMED[name]["a0"], 0.0) / 20 / 1e-4 - 1))
    print(f"- level sets: the formula's gap per quarter at the reference's {len(errs)} 1 bp crossings is 1 bp to within {max(errs):.1e} (relative)")


if __name__ == "__main__":
    main()
