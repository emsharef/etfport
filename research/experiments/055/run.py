"""Experiment 055: claim 113 (D20; mathb/claim113-several-funds-reserve at 1588c595) against the exact two-review program
with two funds and one ETF (harness_n). Registered design: experiments/055-claim113-several-funds-check.md.
Run: uv run python experiments/055/run.py
"""
import importlib.util
import itertools
import json
import zlib
import multiprocessing as mp
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "d16-harness"))
from harness_n import mn_model  # noqa: E402

_p = importlib.util.spec_from_file_location("presets", HERE.parent / "presets.py"); PR = importlib.util.module_from_spec(_p); _p.loader.exec_module(PR)
TOLX, HS = 1e-7, 1e-6
STARTS = {"all-ETF": (0.0, 0.0, 0.9), "all-fund": (0.15, 0.15, 0.0), "fund-heavy": (0.22, 0.10, 0.30), "mixed": (0.05, 0.05, 0.5)}
SETTINGS = [("preset", 1.0), ("revision_var", 4.0), ("etf_sell", 3.0)]
N, E = 2, 2                                   # two funds; the ETF is instrument 2


def model(regime, setting, mult):
    P = PR.PRESETS[regime]; pa = P["alpha_sd"] ** 2; s2 = P["sigma_A"] ** 2
    V = pa ** 2 / (pa + s2) * (mult if setting == "revision_var" else 1.0); fr = P["fund_rate"]
    sell = P["etf_rate"] * (mult if setting == "etf_sell" else 1.0)
    return mn_model(BA=[[1.0], [0.8]], BE=[[1.0]], lam=P["premium"][0], alpha=[P["alpha_mean"], P["alpha_mean"] / 2], premium_sd=P["premium_sd"][0],
                    sigma_f=P["factor_sd"][0], sigma_A=P["sigma_A"], alpha_revision_var=V, cE=[P["etf_fee"]], gamma=P["gamma"],
                    kp=[fr, 1.5 * fr, P["etf_rate"]], km=[fr, 1.5 * fr, sell], cap=[P["fund_cap"], P["fund_cap"], np.inf])


def coords(M, mu0, S0, x):
    """Claim 110's coordinates at review 0: r_i, sigma_EE, v_i, the exposure price m and alpha~."""
    b = M.BA[:, 0]; bE = M.BE[0, 0]; r = b / bE; sEE = S0[E, E]; sf = sEE / bE ** 2
    v = np.diag(S0)[:N] - b ** 2 * sf
    w = x[E] + r @ x[:N]; m = mu0[E] - M.gamma * sEE * w
    return dict(r=r, sEE=sEE, v=v, m=m, at=mu0[:N] - r * mu0[E], struct_err=float(abs(S0[0, 1] - b[0] * b[1] * sf)))


def need_liq(M, nodes, x, h):
    """Per state: need_i (funds and the ETF), need, liq, at root holdings x and cash h."""
    out = []
    for nd in nodes:
        mu, S = M.moments(1, nd["m"]); xh = np.maximum(mu - M.kp, 0) / (M.gamma * np.diag(S))
        ni = (1 + M.kp) * np.maximum(xh - nd["g"] * x, 0)
        xs = (mu[E] + M.km[E]) / (M.gamma * S[E, E])
        liq = max(h, 0) + (1 - M.km[E]) * max(nd["g"][E] * x[E] - max(xs, 0), 0)
        out.append(dict(ni=ni, need=float(ni.sum()), liq=float(liq), mu=mu, S=S))
    return out


def check_2a(M, nodes, x, h):
    """Part 2(a) at root (x, h): covered states' unbudgeted optimum must be budget-feasible."""
    cov = via_etf = fail = 0; worst = 0.0
    for nd, st in zip(nodes, need_liq(M, nodes, x, h)):
        if st["liq"] >= st["need"]:
            cov += 1; via_etf += int(max(h, 0) < st["need"])
            _, _, left = M.one_review(st["mu"], st["S"], x * nd["g"], max(h, 0), budget=False)
            if left < -1e-9:
                fail += 1; worst = min(worst, left)
    return dict(covered=cov, via_etf=via_etf, fail=fail, worst=worst)


def cell(args):
    regime, sname, cash, (setting, mult) = args
    M = model(regime, setting, mult); x0 = np.array(STARTS[sname], float)
    D = M.solve(x0, cash); nodes = D["levels"][1]; xd = D["x"][0][0]; hd = D["h"][0][0]; beta = M.beta
    q = np.array([nd["prob"] for nd in nodes]); G = np.array([nd["g"] for nd in nodes])
    eta0 = D["eta"][0][0]; eta1 = np.array(D["eta"][1]); s1 = np.array(D["s"][1])
    S = beta * (q[:, None] * G * s1).sum(0); eh = eta0 + beta * q @ eta1
    mu0, S0 = M.moments(0, M.m0); cd = coords(M, mu0, S0, xd)
    xmy, emy, hmy = M.one_review(mu0, S0, x0, cash); cm = coords(M, mu0, S0, xmy)
    rec = dict(regime=regime, start=sname, cash=cash, setting=setting, mult=mult, x0=x0.tolist(), x_dyn=xd.tolist(), x_my=xmy.tolist(),
               h_dyn=hd, h_my=hmy, eta0=eta0, eta_hat=eh, eta_my=emy, S=S.tolist(), m_dyn=cd["m"], m_my=cm["m"], struct_err=cd["struct_err"],
               eta1_max=float(eta1.max()), states=len(nodes))
    # 1(b): each fund's clip; the ETF's root line
    clip = []
    for i in range(N):
        base = cd["at"][i] + S[i] + cd["r"][i] * cd["m"] - eh
        lo = (base - (1 + eh) * M.kp[i]) / (M.gamma * cd["v"][i]); hi = (base + (1 + eh) * M.km[i]) / (M.gamma * cd["v"][i])
        a = min(max(min(max(x0[i], lo), hi), 0.0), M.cap[i]); clip.append(float(abs(a - xd[i])))
    val = (cd["m"] + S[E] - eh) / (1 + eh); u = xd[E] - x0[E]
    T = (M.kp[E], M.kp[E]) if u > TOLX else ((-M.km[E], -M.km[E]) if u < -TOLX else (-M.km[E], M.kp[E]))
    etf_line = max(0.0, val - T[1]) if xd[E] <= TOLX else max(0.0, T[0] - val, val - T[1])
    rec["p1b"] = dict(clip_err=clip, etf_line_err=float(etf_line))
    # 2(a): dynamic, one-review and 10 random roots
    rng = np.random.default_rng([55, zlib.crc32(repr((regime, sname, cash, setting)).encode())])
    roots = [("dyn", xd, hd), ("my", xmy, hmy)] + [(f"rand{j}", np.array([rng.uniform(0, M.cap[0]), rng.uniform(0, M.cap[1]), rng.uniform(0, 1)]), rng.uniform(0, 0.1)) for j in range(10)]
    rec["p2a"] = {lab: check_2a(M, nodes, x, h) for lab, x, h in roots}
    # 2(b)
    Ld = need_liq(M, nodes, xd, hd)
    if all(st["liq"] >= st["need"] for st in Ld):
        EG = q @ G
        br = [bool(-beta * EG[i] * M.km[i] - 1e-9 <= S[i] <= beta * EG[i] * M.kp[i] + 1e-9) for i in range(M.n)]
        rec["p2b"] = dict(h_positive=bool(hd > HS), eta1_zero=bool(eta1.max() < 1e-8), eta_hat_eq=bool(abs(eh - eta0) < 1e-8), S_in_brackets=br)
    # 2(c) at both roots
    p2c = {}
    for lab, x, h in (("dyn", xd, hd), ("my", xmy, hmy)):
        Nm = np.array([st["ni"] for st in need_liq(M, nodes, x, h)])
        lhs = float(Nm.sum(1).max()); rhs = float(Nm.max(0).sum())
        common = bool(any(all(Nm[k, i] >= Nm[:, i].max() - 1e-12 for i in range(M.n)) for k in range(len(nodes))))
        eq = bool(rhs - lhs <= 1e-12)
        p2c[lab] = dict(lhs=lhs, rhs=rhs, ok=bool(lhs <= rhs + 1e-12), equality=eq, common_worst=common, iff=bool(eq == common))
    rec["p2c"] = p2c
    # 3(b)
    p3 = []
    for i in range(N):
        ud, um = xd[i] - x0[i], xmy[i] - x0[i]
        inside = all(TOLX < a < M.cap[i] - TOLX for a in (xd[i], xmy[i]))
        same = (ud > TOLX and um > TOLX) or (ud < -TOLX and um < -TOLX)
        kap = M.kp[i] if ud > 0 else -M.km[i]
        terms = [S[i], cd["r"][i] * (cd["m"] - cm["m"]), -(eh - emy) * (1 + kap)]
        pred = sum(terms) / (M.gamma * cd["v"][i])
        p3.append(dict(fund=i, domain=bool(inside and same), move=float(xd[i] - xmy[i]), pred=float(pred), terms=[float(t) for t in terms],
                       err=float(abs(xd[i] - xmy[i] - pred)) if inside and same else None,
                       sign_ok=(bool(np.sign(xd[i] - xmy[i]) == np.sign(pred)) if inside and same and abs(sum(terms)) > 1e-6 else None),
                       dyn_sells_more=bool(xd[i] < xmy[i] - 1e-5)))
    rec["p3b"] = p3
    # Deviation 2 (post hoc, labelled): the display with today's slopes, a^dyn - a^my = [S_i + r_i dm - (eta_hat - eta^my)
    # - (1 + eta_hat) t^dyn + (1 + eta^my) t^my]/(gamma v_i), for every fund strictly inside its box at both roots
    gd, gm = mu0 - M.gamma * S0 @ xd, mu0 - M.gamma * S0 @ xmy; gen = []
    for i in range(N):
        if all(TOLX < a < M.cap[i] - TOLX for a in (xd[i], xmy[i])):
            td = (gd[i] + S[i] - eh) / (1 + eh); tm = (gm[i] - emy) / (1 + emy)
            g = (S[i] + cd["r"][i] * (cd["m"] - cm["m"]) - (eh - emy) - (1 + eh) * td + (1 + emy) * tm) / (M.gamma * cd["v"][i])
            gen.append(dict(fund=i, t_dyn=float(td), t_my=float(tm), pred=float(g), err=float(abs(xd[i] - xmy[i] - g))))
    rec["p3b_general"] = gen
    # part 4
    Cd, Cm = M.cost(xd - x0), M.cost(xmy - x0)
    R = (xd[E] + hd) - (xmy[E] + hmy); rhs = float(np.sum(xmy[:N] - xd[:N]) + Cm - Cd)
    bound = sum((abs(S[i]) + abs(cd["r"][i]) * abs(cd["m"] - cm["m"]) + abs(eh - emy) * (1 + M.kp[i])) / (M.gamma * cd["v"][i]) for i in range(N)) + abs(Cm - Cd)
    Sb = [float(beta * q @ (G[:, i] * np.maximum(M.km[i], eta1 + (1 + eta1) * M.kp[i]))) for i in range(M.n)]
    rec["p4"] = dict(R=float(R), identity_err=float(abs(R - rhs)), bound=float(bound), bound_ok=bool(abs(R) <= bound + 1e-9),
                     domain=bool(all(p["domain"] for p in p3)), S_bound_ok=[bool(abs(S[i]) <= Sb[i] + 1e-9) for i in range(M.n)])
    return rec


def tight_recheck(rec):
    """Deviation 1 (diagnostic): a cell whose 1(b) clip error exceeds the registered 1e-6 is re-solved at tighter solver
    tolerances; the registered result stands as reported."""
    import harness_n as H
    old = dict(H.OPT); H.OPT.update(tol_gap_abs=1e-14, tol_gap_rel=1e-13, tol_feas=1e-13, max_iter=2000)
    try:
        r = cell((rec["regime"], rec["start"], rec["cash"], (rec["setting"], rec["mult"])))
    finally:
        H.OPT.clear(); H.OPT.update(old)
    return r["p1b"]["clip_err"]


def fmt_t(gg):
    return f"{gg['t_dyn']:+.4f} / {gg['t_my']:+.4f}" if gg else "fund at a bound"


def report(C):
    L = ["# Experiment 055: summary (generated by run.py from summary.json)", "",
         "Claim 113 at 1588c595. Tested cells only (AGENTS.md rule 22).", ""]
    ce = max(max(c["p1b"]["clip_err"]) for c in C); el = max(c["p1b"]["etf_line_err"] for c in C)
    over = [c for c in C if max(c["p1b"]["clip_err"]) > 1e-6]
    L += [f"- **1(b):** largest fund-clip error {ce:.2e} ({len(over)} cell(s) above 1e-6"
          + (": " + "; ".join(f"{c['regime']} {c['start']} cash {c['cash']} {c['setting']}: {max(c['p1b']['clip_err']):.2e}, at tight tolerances {max(c['tight_clip_err']):.1e}" for c in over) if over else "")
          + f"); the largest ETF root-line error is {el:.1e}."]
    tot = {k: sum(r[k] for c in C for r in c["p2a"].values()) for k in ("covered", "via_etf", "fail")}
    L += [f"- **2(a):** {sum(len(c['p2a']) for c in C)} roots (dynamic, one-review and 10 random per cell), {sum(c['states'] * len(c['p2a']) for c in C)} states: "
          f"{tot['covered']} covered, of which {tot['via_etf']} only through the ETF's proceeds; {tot['fail']} failures."]
    b = [c for c in C if "p2b" in c]
    L += [f"- **2(b):** {len(b)} cells with every state covered at the dynamic root (h^+_0 > 0 in {sum(c['p2b']['h_positive'] for c in b)}): eta_1 = 0 in "
          f"{sum(c['p2b']['eta1_zero'] for c in b)}, eta_hat_0 = eta_0 in {sum(c['p2b']['eta_hat_eq'] for c in b)}, every S_i in claim 029's bracket in {sum(all(c['p2b']['S_in_brackets']) for c in b)}."]
    for lab in ("dyn", "my"):
        L += [f"- **2(c) at the {'dynamic' if lab == 'dyn' else 'one-review'} root:** the bound holds in {sum(c['p2c'][lab]['ok'] for c in C)}/{len(C)}; equality in "
              f"{sum(c['p2c'][lab]['equality'] for c in C)}, a common worst state in {sum(c['p2c'][lab]['common_worst'] for c in C)}, and the iff in {sum(c['p2c'][lab]['iff'] for c in C)}/{len(C)}."]
    p3 = [p for c in C for p in c["p3b"]]; d = [p for p in p3 if p["domain"]]
    L += [f"- **3(b):** {len(d)} of {len(p3)} fund-cells in the domain; largest error {max(p['err'] for p in d):.1e}; the sign statement holds in "
          f"{sum(p['sign_ok'] is True for p in d)} of the {sum(p['sign_ok'] is not None for p in d)} where the right side exceeds 1e-6."]
    g = [x for c in C for x in c["p3b_general"]]
    L += [f"- **Deviation 2 (post hoc):** the display with today's slopes is exact for all {len(g)} fund-cells strictly inside the box at both roots (largest error {max(x['err'] for x in g):.1e})."]
    L += [f"- **Part 4:** wealth-identity error {max(c['p4']['identity_err'] for c in C):.1e}; the |R| bound holds in {sum(c['p4']['bound_ok'] for c in C)}/{len(C)} "
          f"(the stated domain, both funds on common trading pieces, contains {sum(c['p4']['domain'] for c in C)} cells); the |S_i| bound holds in {sum(all(c['p4']['S_bound_ok']) for c in C)}/{len(C)}."]
    L += ["", "## The cells where the dynamic policy sells a fund beyond the one-review policy", "",
          "| regime | start | cash | setting | fund | move | 3(b) domain | S_i | r_i dm | -(d eta)(1 + kappa) | t^dyn / t^my (general form) |", "|---|---|---|---|---|---|---|---|---|---|---|"]
    for c in C:
        for p in c["p3b"]:
            if p["dyn_sells_more"]:
                gg = next((x for x in c["p3b_general"] if x["fund"] == p["fund"]), None)
                L.append(f"| {c['regime'].split('-')[0]} | {c['start']} | {c['cash']} | {c['setting']} | {p['fund'] + 1} | {p['move']:+.4f} | {'y' if p['domain'] else 'n'} | "
                         f"{p['terms'][0]:+.2e} | {p['terms'][1]:+.2e} | {p['terms'][2]:+.1e} | {fmt_t(gg)} |")
    (HERE / "report.md").write_text("\n".join(L) + "\n")


def main():
    cells = list(itertools.product(("equity-style", "fixed-income-style"), STARTS, (0.30, 0.02), SETTINGS))
    with mp.Pool(8) as pool:
        res = pool.map(cell, cells, chunksize=1)
    for r in res:
        if max(r["p1b"]["clip_err"]) > 1e-6:
            r["tight_clip_err"] = tight_recheck(r)
    report(res)
    json.dump(dict(cells=res, statement="claim 113 at 1588c595 (mathb/claim113-several-funds-reserve)"), open(HERE / "summary.json", "w"), indent=0,
              default=lambda o: o.tolist() if hasattr(o, "tolist") else (bool(o) if isinstance(o, np.bool_) else float(o)))
    print("done", len(res))


if __name__ == "__main__":
    main()
