"""Experiment 057: claim 114 (D24, M9; main at 9a6ffb38) on the M9 harness: 1a, 1b, part 2's up-down identity, 3a-3b.
Registered design: experiments/057-claim114-m9-target-move-check.md.  Run: uv run python experiments/057/run.py
"""
import importlib.util
import itertools
import json
import multiprocessing as mp
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "d16-harness"))
from harness_n import mn_model  # noqa: E402

_p = importlib.util.spec_from_file_location("presets", HERE.parent / "presets.py"); PR = importlib.util.module_from_spec(_p); _p.loader.exec_module(PR)
PHIS = [(1.0, 0.5), (0.9, 0.5), (0.7, 0.9)]
QS = [(0.0, 0.0), (1e-6, 1e-7), (0.0, 1e-6)]
SHIFTS = [0.006, -0.006]
STARTS = [0.0, 0.05, 0.2]
TOLX, HS = 1e-7, 1e-6


def model(regime, phi, q, shift, bA=1.0):
    P = PR.PRESETS[regime]
    return mn_model(BA=[[bA]], BE=[[1.0]], lam=P["premium"][0], alpha=P["alpha_mean"], premium_sd=P["premium_sd"][0], sigma_f=P["factor_sd"][0],
                    sigma_A=P["sigma_A"], alpha_sd=P["alpha_sd"], cE=[P["etf_fee"]], gamma=P["gamma"], kp=[P["fund_rate"], P["etf_rate"]],
                    km=[P["fund_rate"], P["etf_rate"]], cap=[P["fund_cap"], np.inf], phi=phi, q=q, theta_bar=[P["premium"][0], P["alpha_mean"] + shift])


def spec_filter(M, t):
    """Claim 114's objects in M9's transformed coordinates (H = I, R = diag(sigma_f^2, sigma_A^2)): K_t, P^u_t, V_t."""
    P = M.P(t); R = np.diag([M.Sz[0, 0], M.Sz[1, 1]]); K = P @ np.linalg.inv(P + R); Pu = P - K @ P
    return P, K, Pu, M.Phi @ (P - Pu) @ M.Phi.T, R


def xstar(M, t, m):
    mu, S = M.moments(t, m); return np.linalg.solve(M.gamma * S, mu), mu, S


def check_1a(M):
    P0, K0, Pu0, V0, R = spec_filter(M, 0); nodes = M.tree(2)[1]
    x0, mu0, S0 = xstar(M, 0, M.m0); S1 = M.moments(1, M.m0)[1]; iS1, iS0 = np.linalg.inv(M.gamma * S1), np.linalg.inv(M.gamma * S0)
    I = np.eye(2)
    dp = iS1 @ M.G @ (M.Phi - I) @ (M.m0 - M.theta_bar) + (iS1 - iS0) @ mu0
    err = 0.0; dus, pr = [], []
    for nd in nodes:
        y = nd["g"] - 1.0; f = (y[1] + M.cE[0]) / M.BE[0, 0]
        nu = np.array([f - M.m0[0], y[0] - M.BA[0, 0] * f - M.m0[1]])
        du = iS1 @ M.G @ M.Phi @ K0 @ nu
        x1, _, _ = xstar(M, 1, nd["m"]); err = max(err, float(np.max(np.abs(x1 - x0 - dp - du))))
        dus.append(du); pr.append(nd["prob"])
    dus, pr = np.array(dus), np.array(pr)
    mean = pr @ dus; cov = dus.T @ np.diag(pr) @ dus; cth = iS1 @ M.G @ V0 @ M.G.T @ iS1
    return dict(decomp_err=err, mean_err=float(np.max(np.abs(mean))), cov_rel_err=float(np.max(np.abs(cov - cth)) / np.max(np.abs(cth)))), dp, dus, pr


def fixed_point(phi, q, s):
    b = s * (1 - phi ** 2) - q
    return (-b + np.sqrt(b * b + 4 * q * s)) / 2


def check_1b(M, T=10):
    rec = dict(recursion_err=0.0, iff_ok=0, iff_fail=0, knife=0, psd_below=0, psd_below_all_rise=0, psd_above=0, psd_above_all_fall=0, steps=[])
    kap = M.kp + M.km
    for t in range(T):
        P, K, Pu, V, R = spec_filter(M, t); P1 = M.P(t + 1)
        rec["recursion_err"] = max(rec["recursion_err"], float(np.max(np.abs((P1 - P) - (M.Q - (P - M.Phi @ Pu @ M.Phi.T))))))
        w0 = kap / (M.gamma * np.diag(M.moments(t, M.m0)[1])); w1 = kap / (M.gamma * np.diag(M.moments(t + 1, M.m0)[1]))
        cond = np.diag(M.G @ (M.Q - (P - M.Phi @ Pu @ M.Phi.T)) @ M.G.T)
        for i in range(2):
            if abs(cond[i]) < 1e-14:
                rec["knife"] += 1
            elif (w1[i] > w0[i]) == (cond[i] < 0):
                rec["iff_ok"] += 1
            else:
                rec["iff_fail"] += 1
        ev = np.linalg.eigvalsh(P1 - P)
        if ev.max() <= 1e-18:
            rec["psd_below"] += 1; rec["psd_below_all_rise"] += int(all(w1 >= w0 - 1e-15))
        if ev.min() >= -1e-18:
            rec["psd_above"] += 1; rec["psd_above_all_fall"] += int(all(w1 <= w0 + 1e-15))
        rec["steps"].append(dict(t=t, cond=cond.tolist(), width_change=(w1 - w0).tolist(), psd=("below" if ev.max() <= 1e-18 else ("above" if ev.min() >= -1e-18 else "neither"))))
    # convergence per block: iterate the scalar map to t = 400
    conv = []
    R = np.diag([M.Sz[0, 0], M.Sz[1, 1]])
    for k in range(2):
        phi, q, s = M.Phi[k, k], M.Q[k, k], R[k, k]; p = M.P0[k, k]; ps = [p]
        for _ in range(400):
            p = phi ** 2 * p * s / (p + s) + q; ps.append(p)
        d = np.diff(ps); mono = bool(np.all(d <= 1e-30) or np.all(d >= -1e-30)); pst = fixed_point(phi, q, s)
        c = dict(block=k, monotone=mono, p400=ps[-1], p_star=float(pst), gap=float(abs(ps[-1] - pst)), ok=bool(mono and abs(ps[-1] - pst) < 1e-15),
                 harness_err=float(abs(M.P(12)[k, k] - ps[12])))
        if not c["ok"]:                                    # Deviation 1 (diagnostic): slow convergence when phi = 1
            if q == 0 and phi == 1:
                c["dev1"] = dict(kind="1/t (information form)", closed_form_err=float(max(abs(ps[t] - 1 / (1 / M.P0[k, k] + t / s)) for t in range(401))))
            else:
                pp = ps[-1]
                for _ in range(20000):
                    pp = phi ** 2 * pp * s / (pp + s) + q
                c["dev1"] = dict(kind="geometric, slow", rate=float(phi ** 2 * s ** 2 / (pst + s) ** 2), gap_at_20400=float(abs(pp - pst)))
        conv.append(c)
    rec["convergence"] = conv
    return rec


def check_2(M, dp, dus, pr):
    out = []
    c0 = M.gamma * np.diag(M.moments(0, M.m0)[1])
    for i in range(2):
        vals, ws = [], []                                  # the law's atoms, merged within 1e-13
        for val, w in zip(dus[:, i], pr):
            j = next((j for j, u in enumerate(vals) if abs(u - val) < 1e-13), None)
            if j is None:
                vals.append(val); ws.append(w)
            else:
                ws[j] += w
        mirror = lambda a: sum(w for u, w in zip(vals, ws) if abs(u + a) < 1e-13)
        sym = all(abs(mirror(a) - w) < 1e-12 for a, w in zip(vals, ws))
        x = dus[:, i]; a = abs(dp[i])
        U = float(pr @ (x > -dp[i])); D = float(pr @ (x < -dp[i]))
        rec = dict(inst=i, dp=float(dp[i]), U=U, D=D, symmetric=sym)
        if sym:
            if dp[i] > 0:
                target = float(pr @ ((x > -a) & (x <= a)))
            elif dp[i] < 0:
                target = -float(pr @ ((x >= -a) & (x < a)))
            else:
                target = 0.0
            rec["identity_err"] = abs((U - D) - target)
            kap = M.kp[i]; tau = M.beta * kap * (U - D) / c0[i]
            atom = float(pr @ (np.abs(x + dp[i]) < 1e-15))
            rec["tau_sign_ok"] = bool(tau == 0 or np.sign(tau) == np.sign(dp[i]))
            if atom == 0.0:
                rec["tau_abs_err"] = float(abs(abs(tau) - M.beta * kap * float(pr @ (np.abs(x) <= a)) / c0[i]))
        out.append(rec)
    return out


def check_3(M, a0):
    x0 = np.array([a0, 0.4]); cash = 1.0; mu0, S0 = M.moments(0, M.m0)
    xmy, emy, hmy = M.one_review(mu0, S0, x0, cash, frozen=(1,))
    nodes = M.tree(2)[1]; q = np.array([nd["prob"] for nd in nodes]); gA = np.array([nd["g"][0] for nd in nodes])
    moves, etas, lefts = [], [], []
    for nd in nodes:
        mu, S = M.moments(1, nd["m"]); xm = xmy * nd["g"]; x1, e1, h1 = M.one_review(mu, S, xm, hmy, frozen=(1,))
        moves.append(x1[0] - xm[0]); etas.append(e1); lefts.append(h1)
    moves = np.array(moves); etas = np.array(etas)
    case = "3a" if np.all(moves > TOLX) else ("3b" if np.all(moves < -TOLX) else None)
    rec = dict(a0=a0, a_my=float(xmy[0]), case=case)
    if case is None:
        return rec
    D = M.solve(x0, cash, frozen=(1,)); xd = D["x"][0][0]
    slack = bool(hmy > HS and min(lefts) > HS and D["h"][0][0] > HS and min(D["h"][1]) > HS)
    rec.update(a_dyn=float(xd[0]), hyp=slack)
    if not slack:
        return rec
    EgA = float(q @ gA); kp, km = M.kp[0], M.km[0]
    t1 = kp if case == "3a" else -km
    S_my = float(M.beta * q @ (gA * (etas + (1 + etas) * t1))); bracket = M.beta * EgA * t1
    S_dyn = float(M.beta * q @ (gA * np.array(D["s"][1])[:, 0]))
    rec.update(S_my=S_my, S_my_err=abs(S_my - bracket), order_ok=bool(xd[0] >= xmy[0] - TOLX if case == "3a" else xd[0] <= xmy[0] + TOLX))
    trade = xd[0] - x0[0]
    if (case == "3a" and trade > TOLX) or (case == "3b" and trade < -TOLX):
        g0 = float((mu0 - M.gamma * S0 @ xd)[0]); thr = (1 - M.beta * EgA) * t1
        x1d = np.array([D["x"][1][k][0] - xd[0] * nodes[k]["g"][0] for k in range(len(nodes))])
        trades_all = bool(np.all(x1d > TOLX) if case == "3a" else np.all(x1d < -TOLX))
        rec.update(line_checked=True, line_err=abs(g0 - thr), S_dyn_err=abs(S_dyn - bracket), S_dyn=S_dyn, bracket=bracket,
                   line_with_S_dyn_err=abs(g0 + S_dyn - t1), dyn_tomorrow_trades_all=trades_all, dyn_tomorrow_trades=int(np.sum(x1d > TOLX) if case == "3a" else np.sum(x1d < -TOLX)),
                   threshold_actual=float(t1 - S_dyn), threshold_claimed=float(thr), bound_ok=bool(abs(S_dyn) <= abs(bracket) + 1e-12))
    else:
        rec.update(line_checked=False)
    return rec


def run_model(args):
    regime, phi, q, shift = args
    M = model(regime, phi, q, shift)
    r1a, dp, dus, pr = check_1a(M)
    return dict(regime=regime, phi=phi, q=q, shift=shift, p1a=r1a, p1b=check_1b(M), p2=check_2(M, dp, dus, pr), p3=[check_3(M, a0) for a0 in STARTS])


def named():
    out = {}
    for name, kw in (("red", dict(regime="equity-style", phi=(1.0, 1.0), q=(0.0, 1e-4), shift=0.0)),
                     ("lean", dict(regime="equity-style", phi=(1.0, 1.0), q=(1e-6, 0.0), shift=0.0, bA=0.9))):
        M = model(**kw); r = check_1b(M); s0 = r["steps"][0]
        P, K, Pu, V, R = spec_filter(M, 0); Qbelow = bool(np.linalg.eigvalsh(M.Q - (P - M.Phi @ Pu @ M.Phi.T)).max() <= 1e-18)
        out[name] = dict(p1b=r, fund_width_change=s0["width_change"][0], etf_width_change=s0["width_change"][1], psd=s0["psd"], Q_psd_below=Qbelow)
    return out


def named_spec():
    """Deviation 2: the named 1b instances at the claim's worked-example inputs (b_A = 0.9, b_E = 1, sigma_f = 8.01%,
    sigma_A = 6.32%, P_0 = diag(1.6e-5, 4e-4)): red's Q = diag(0, 1e-4); lean's described instance (a noise-dominant lambda
    block, a learning-dominant alpha block; the claim gives no numbers) built as Q = diag(1e-5, 0)."""
    P = PR.PRESETS["equity-style"]; out = {}
    for name, q in (("red", (0.0, 1e-4)), ("lean", (1e-5, 0.0))):
        M = mn_model(BA=[[0.9]], BE=[[1.0]], lam=0.010, alpha=0.004, premium_sd=np.sqrt(1.6e-5), sigma_f=0.0801, sigma_A=0.0632, alpha_sd=np.sqrt(4e-4),
                     cE=[0.0005], gamma=P["gamma"], kp=[P["fund_rate"], P["etf_rate"]], km=[P["fund_rate"], P["etf_rate"]], cap=[1.0, np.inf], phi=1.0, q=q)
        r = check_1b(M, T=3); s0 = r["steps"][0]
        Pm, K, Pu, V, R = spec_filter(M, 0); Qbelow = bool(np.linalg.eigvalsh(M.Q - (Pm - M.Phi @ Pu @ M.Phi.T)).max() <= 1e-18)
        out[name] = dict(q=q, iff_ok=r["iff_ok"], iff_fail=r["iff_fail"], fund_width_change=s0["width_change"][0], etf_width_change=s0["width_change"][1], psd=s0["psd"], Q_psd_below=Qbelow)
    return out


def report(res, nm):
    L = ["# Experiment 057: summary (generated by run.py from summary.json)", "", "Claim 114 at 9a6ffb38. Tested models only (AGENTS.md rule 22).", ""]
    L += [f"- **1a:** {len(res)} models; decomposition error {max(r['p1a']['decomp_err'] for r in res):.1e}; E Delta^u {max(r['p1a']['mean_err'] for r in res):.1e}; "
          f"covariance relative error {max(r['p1a']['cov_rel_err'] for r in res):.1e}."]
    b = [r["p1b"] for r in res]
    conv = [c for x in b for c in x["convergence"]]
    L += [f"- **1b:** recursion error {max(x['recursion_err'] for x in b):.1e}; the per-instrument iff holds in {sum(x['iff_ok'] for x in b)} of "
          f"{sum(x['iff_ok'] + x['iff_fail'] for x in b)} steps (knife edges set aside: {sum(x['knife'] for x in b)}); psd-below steps {sum(x['psd_below'] for x in b)}, all widths rise in "
          f"{sum(x['psd_below_all_rise'] for x in b)}; psd-above steps {sum(x['psd_above'] for x in b)}, all widths fall in {sum(x['psd_above_all_fall'] for x in b)}; "
          f"blocks monotone {sum(c['monotone'] for c in conv)}/{len(conv)}, within 1e-15 of the fixed point at t = 400: {sum(c['gap'] < 1e-15 for c in conv)}/{len(conv)} "
          f"(largest gap {max(c['gap'] for c in conv):.1e}); the harness's P_12 against the scalar map {max(c['harness_err'] for c in conv):.1e}."]
    for k, v in nm.items():
        L += [f"- **1b, {k}'s instance:** fund width change {v['fund_width_change']:+.2e}, ETF {v['etf_width_change']:+.2e}, P_1 - P_0 {v['psd']}, Q psd-below what learning removes: {v['Q_psd_below']}."]
    for k, v in named_spec().items():
        L += [f"- **Deviation 2, {k}'s instance at the worked-example inputs (Q = diag{v['q']}):** fund width change {v['fund_width_change']:+.2e}, ETF {v['etf_width_change']:+.2e}, "
              f"P_1 - P_0 {v['psd']}, Q psd-below: {v['Q_psd_below']}; iff {v['iff_ok']}/{v['iff_ok'] + v['iff_fail']}."]
    d1 = [c for x in b for c in x["convergence"] if "dev1" in c]
    L += [f"- **Deviation 1 (convergence diagnostic):** the {len(d1)} blocks not within 1e-15 at t = 400 all have phi = 1: "
          f"{sum(c['dev1']['kind'].startswith('1/t') for c in d1)} with q = 0 follow the information form 1/(1/p_0 + t/s) to "
          f"{max((c['dev1'].get('closed_form_err', 0) for c in d1), default=0):.1e}; {sum(c['dev1']['kind'].startswith('geometric') for c in d1)} with q > 0 contract at rate "
          f"{max((c['dev1'].get('rate', 0) for c in d1), default=0):.4f} and are within {max((c['dev1'].get('gap_at_20400', 0) for c in d1), default=0):.1e} of p* at t = 20,400."]
    p2 = [x for r in res for x in r["p2"]]; sym = [x for x in p2 if x["symmetric"]]
    L += [f"- **Part 2:** {len(p2)} instrument-models, symmetric laws {len(sym)}; identity error {max(x['identity_err'] for x in sym):.1e}; tau's sign {sum(x['tau_sign_ok'] for x in sym)}/{len(sym)}; "
          f"|tau| display error {max((x['tau_abs_err'] for x in sym if 'tau_abs_err' in x), default=float('nan')):.1e} over {sum('tau_abs_err' in x for x in sym)} without an atom at -Delta^p."]
    p3 = [x for r in res for x in r["p3"]]
    for case in ("3a", "3b"):
        c = [x for x in p3 if x["case"] == case]; h = [x for x in c if x.get("hyp")]; ln = [x for x in h if x.get("line_checked")]
        L += [f"- **{case}:** precondition in {len(c)} of {len(p3)} cells, hypotheses in {len(h)}; S_A at the one-review tomorrow error "
              f"{max((x['S_my_err'] for x in h), default=float('nan')):.1e}; order holds {sum(x['order_ok'] for x in h)}/{len(h)}; line checked in {len(ln)}: marginal error "
              f"{max((x['line_err'] for x in ln), default=float('nan')):.1e} (above 1e-7 in {sum(x['line_err'] > 1e-7 for x in ln)}), S_A (duals) at its bracket end {max((x['S_dyn_err'] for x in ln), default=float('nan')):.1e}."]
        if ln:
            L += [f"  - The root line with the dynamic S_A holds to {max(x['line_with_S_dyn_err'] for x in ln):.1e}; |S_A| within the bracket in {sum(x['bound_ok'] for x in ln)}/{len(ln)}; "
                  f"the dynamic root's tomorrow trades the fund in every state in {sum(x['dyn_tomorrow_trades_all'] for x in ln)}/{len(ln)} "
                  f"(the claimed threshold is exact there: largest error {max((x['line_err'] for x in ln if x['dyn_tomorrow_trades_all']), default=float('nan')):.1e})."]
    (HERE / "report.md").write_text("\n".join(L) + "\n")


def main():
    grid = list(itertools.product(PR.PRESETS, PHIS, QS, SHIFTS))
    with mp.Pool(8) as pool:
        res = pool.map(run_model, grid, chunksize=1)
    nm = named(); report(res, nm)
    json.dump(dict(models=res, named=nm, statement="claim 114 at 9a6ffb38"), open(HERE / "summary.json", "w"), indent=0,
              default=lambda o: o.tolist() if hasattr(o, "tolist") else (bool(o) if isinstance(o, np.bool_) else float(o)))
    print("done", len(res))


if __name__ == "__main__":
    main()
