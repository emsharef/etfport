"""Experiment 056: claim 048 (D23; math/claim048-d23-many-etfs at 4da05a03) against the exact two-review program with two
funds and two frictionless ETFs spanning two factors (harness_n). Registered design: experiments/056-claim048-many-etfs-check.md.
Run: uv run python experiments/056/run.py   (writes summary.json and report.md)
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
TOLX = 1e-7
N, M_, K = 2, 2, 2
BA = np.array([[1.0, 0.3], [0.6, 0.8]]); BE = np.array([[1.0, 0.0], [0.5, 1.0]])
STARTS = {"ETF-only": (0.0, 0.0, 0.6, 0.3), "fund-light-ETF": (0.15, 0.15, 0.1, 0.05), "fund-heavy": (0.22, 0.10, 0.3, 0.1), "mixed": (0.05, 0.05, 0.4, 0.2)}
SETTINGS = [("preset", 1.0), ("revision_var", 4.0)]


SUPPLEMENT = list(itertools.product((0.004, 0.006), (4e-5, 8e-5), (0.30, 0.50)))     # Deviation 1: (fund-1 alpha, V, cash)


def model_supp(alpha, V):
    """Deviation 1 (post hoc, labelled): equity-style preset with fund 1's alpha mean raised, both caps 1.0 and a large
    revision variance, found by a 32-point probe so that tomorrow's cash price is positive while part 2's hypotheses hold."""
    P = PR.PRESETS["equity-style"]; fr = P["fund_rate"]
    return mn_model(BA=BA, BE=BE, lam=list(P["premium"]), alpha=[alpha, alpha / 2], premium_sd=list(P["premium_sd"]), sigma_f=list(P["factor_sd"]),
                    sigma_A=P["sigma_A"], alpha_revision_var=V, cE=[0.0, 0.0], gamma=P["gamma"],
                    kp=[fr, 1.5 * fr, 0.0, 0.0], km=[fr, 1.5 * fr, 0.0, 0.0], cap=[1.0, 1.0, np.inf, np.inf])


def model(regime, setting, mult):
    P = PR.PRESETS[regime]; pa = P["alpha_sd"] ** 2; s2 = P["sigma_A"] ** 2; fr = P["fund_rate"]
    V = pa ** 2 / (pa + s2) * (mult if setting == "revision_var" else 1.0)
    return mn_model(BA=BA, BE=BE, lam=list(P["premium"]), alpha=[P["alpha_mean"], P["alpha_mean"] / 2], premium_sd=list(P["premium_sd"]),
                    sigma_f=list(P["factor_sd"]), sigma_A=P["sigma_A"], alpha_revision_var=V, cE=[0.0, 0.0], gamma=P["gamma"],
                    kp=[fr, 1.5 * fr, 0.0, 0.0], km=[fr, 1.5 * fr, 0.0, 0.0], cap=[P["fund_cap"], P["fund_cap"], np.inf, np.inf])


def separated_root(M, x0, S, eh):
    """Claim 048 part 2: the ETF reserve problem and the fund alpha problem at the tilted inputs."""
    R = np.linalg.inv(M.BE); one = np.ones(M_); r = M.BA @ R                      # r[i] = R' (B^A_i)'
    lam, alp = M.m0[:K], M.m0[K:]
    SA, SE = S[:N], S[N:]
    lam_res = lam + R @ (SE - eh * one)
    alp_res = alp + SA - r @ SE - eh * (1 - r @ one)
    Sf = M.factor_cov(0); v = M.Sz[K:K + N, K:K + N].diagonal() + M.P(0)[K:, K:].diagonal()
    b0 = np.linalg.solve(M.gamma * Sf, lam_res)
    a = np.empty(N)
    for i in range(N):
        lo = (alp_res[i] - (1 + eh) * M.kp[i]) / (M.gamma * v[i]); hi = (alp_res[i] + (1 + eh) * M.km[i]) / (M.gamma * v[i])
        a[i] = min(max(min(max(x0[i], lo), hi), 0.0), M.cap[i])
    xE = R.T @ (b0 - M.BA.T @ a)
    return np.concatenate([a, xE]), b0


def cell(args):
    regime, sname, cash, (setting, mult) = args
    if regime == "supplement":
        M = model_supp(setting, mult); x0 = np.array((0.0, 0.0, 0.3, 0.2))
    else:
        M = model(regime, setting, mult); x0 = np.array(STARTS[sname], float)
    D = M.solve(x0, cash); nodes = D["levels"][1]; xd = D["x"][0][0]; beta = M.beta
    q = np.array([nd["prob"] for nd in nodes]); G = np.array([nd["g"] for nd in nodes])
    eta0 = D["eta"][0][0]; eta1 = np.array(D["eta"][1]); s1 = np.array(D["s"][1])
    S = beta * (q[:, None] * G * s1).sum(0); eh = eta0 + beta * q @ eta1
    mu0, S0 = M.moments(0, M.m0); xmy, emy, hmy = M.one_review(mu0, S0, x0, cash)
    R = np.linalg.inv(M.BE); Sf = M.factor_cov(0)
    rec = dict(regime=regime, start=sname, cash=cash, setting=setting, mult=mult, x0=x0.tolist(), x_dyn=xd.tolist(), x_my=xmy.tolist(),
               h_dyn=D["h"][0][0], eta0=eta0, eta_hat=eh, eta_my=emy, eta1_max=float(eta1.max()), S=S.tolist(), states=len(nodes))
    reasons = ([] if eta0 < 1e-9 else ["today's budget binds"]) + ([] if min(xd[N:]) > TOLX else ["an ETF at zero"])
    rec["hyp"] = dict(hold=not reasons, reasons=reasons)
    tilt = R @ (S[N:] - eh * np.ones(M_)); rec["tilt"] = tilt.tolist(); rec["tilt_nonzero"] = bool(np.max(np.abs(tilt)) > 1e-9)
    if not reasons:
        xs, b0 = separated_root(M, x0, S, eh)
        rec["p2"] = dict(root_err=float(np.max(np.abs(xs - xd))), exposure_err=float(np.max(np.abs(b0 - M.BA.T @ xd[:N] - M.BE.T @ xd[N:]))),
                         fund_err=float(np.max(np.abs(xs[:N] - xd[:N]))), etf_err=float(np.max(np.abs(xs[N:] - xd[N:]))))
        # part 3, the frictionless-tomorrow form: S_E = beta E[g_E eta_1], tilt = beta R E[(g_E - 1) eta_1]
        SE_ft = beta * (q[:, None] * G[:, N:] * eta1[:, None]).sum(0); tilt_ft = beta * R @ (q[:, None] * (G[:, N:] - 1) * eta1[:, None]).sum(0)
        rec["p3_frictionless"] = dict(SE_err=float(np.max(np.abs(SE_ft - S[N:]))), tilt_err=float(np.max(np.abs(tilt_ft - tilt))))
        if emy < 1e-9 and min(xmy[N:]) > TOLX:
            lhs = xd[N:] - xmy[N:]
            rhs = R.T @ np.linalg.solve(M.gamma * Sf, tilt) - R.T @ M.BA.T @ (xd[:N] - xmy[:N])
            rec["p3"] = dict(err=float(np.max(np.abs(lhs - rhs))), lhs=lhs.tolist(), rhs=rhs.tolist())
        else:
            rec["p3"] = dict(err=None, reason="the one-review root is not untilted (eta^my > 0 or an ETF at zero)")
    return rec


def p3err(c):
    e = c.get("p3", {}).get("err")
    return f"{e:.1e}" if e is not None else "-"


def report(Call):
    L = []
    for lab, C in (("Registered grid (32 cells)", [c for c in Call if c["regime"] != "supplement"]),
                   ("Deviation 1: supplementary cells (post hoc, labelled; 8 cells, equity-style, fund-1 alpha x setting, V x mult)", [c for c in Call if c["regime"] == "supplement"])):
        L += ["", f"## {lab}", ""] + report_block(C)
    (HERE / "report.md").write_text("# Experiment 056: summary (generated by run.py from summary.json)\n\nClaim 048 at 4da05a03. Tested cells only (AGENTS.md rule 22).\n" + "\n".join(L) + "\n")


def report_block(C):
    h = [c for c in C if c["hyp"]["hold"]]
    L = [f"- Part 2's hypotheses (eta_0 = 0, both ETFs strictly inside) hold in {len(h)} of {len(C)} cells; they fail in {len(C) - len(h)}: "
          + ", ".join(f"{r}: {sum(r in c['hyp']['reasons'] for c in C)}" for r in ("today's budget binds", "an ETF at zero")) + "."]
    if h:
        L += [f"- **Part 2, the separated root:** largest holding error {max(c['p2']['root_err'] for c in h):.1e} (funds {max(c['p2']['fund_err'] for c in h):.1e}, "
              f"ETFs {max(c['p2']['etf_err'] for c in h):.1e}); exposure error {max(c['p2']['exposure_err'] for c in h):.1e}; failures above 1e-6: {sum(c['p2']['root_err'] > 1e-6 for c in h)}."]
        t = [c for c in h if c["tilt_nonzero"]]
        L += [f"- A nonzero reserve tilt (some eta_1 > 0): {len(t)} of the {len(h)} cells" + (f"; there the largest error is {max(c['p2']['root_err'] for c in t):.1e}." if t else ".")]
        p3 = [c for c in h if c["p3"]["err"] is not None]
        L += [f"- **Part 3, the exposure identity:** {len(p3)} cells with an untilted one-review root; largest error {max(c['p3']['err'] for c in p3):.1e}" if p3 else "- Part 3: no cell with an untilted one-review root."]
        L += [f"- **Part 3, the frictionless-tomorrow form:** S_E = beta E[g_E eta_1] to {max(c['p3_frictionless']['SE_err'] for c in h):.1e}, "
              f"the tilt = beta R E[(g_E - 1) eta_1] to {max(c['p3_frictionless']['tilt_err'] for c in h):.1e}."]
    L += ["", "| regime | start | cash | setting | hypotheses | eta_1 max | tilt | part 2 error | part 3 error |", "|---|---|---|---|---|---|---|---|---|"]
    for c in C:
        L.append(f"| {c['regime'].split('-')[0]} | {c['start']} | {c['cash']} | {c['setting']} x{c['mult']:g} | {'hold' if c['hyp']['hold'] else '; '.join(c['hyp']['reasons'])} | "
                 f"{c['eta1_max']:.2e} | ({c['tilt'][0]:+.1e}, {c['tilt'][1]:+.1e}) | {c['p2']['root_err']:.1e} | "
                 f"{p3err(c)} |"
                 if c["hyp"]["hold"] else
                 f"| {c['regime'].split('-')[0]} | {c['start']} | {c['cash']} | {c['setting']} x{c['mult']:g} | {'; '.join(c['hyp']['reasons'])} | {c['eta1_max']:.2e} | - | - | - |")
    return L


def main():
    cells = list(itertools.product(("equity-style", "fixed-income-style"), STARTS, (0.30, 0.02), SETTINGS))
    cells += [("supplement", "ETF-only (0, 0, 0.3, 0.2)", cash, (alpha, V)) for alpha, V, cash in SUPPLEMENT]
    with mp.Pool(8) as pool:
        res = pool.map(cell, cells, chunksize=1)
    report(res)
    json.dump(dict(cells=res, statement="claim 048 at 4da05a03 (math/claim048-d23-many-etfs)"), open(HERE / "summary.json", "w"), indent=0,
              default=lambda o: o.tolist() if hasattr(o, "tolist") else (bool(o) if isinstance(o, np.bool_) else float(o)))
    print("done", len(res))


if __name__ == "__main__":
    main()
