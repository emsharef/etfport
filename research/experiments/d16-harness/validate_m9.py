"""Validation of harness_n's M9 extension (D24 preparation; PM's note 2026-09-30-d24-m9-prep). No findings.
  (a) Phi = I and Q = 0, passed explicitly, reproduce experiment 054's 144 cells (dynamic and one-review roots) and
      experiment 048's 72 cells (dynamic value and root);
  (b) the filter against M9's scalar-block formulas (model/SPEC.md M9 on mathb/claim114-d24-target-move at eb786cb5)
      at every review-1 node, with Phi != I, Q != 0 and theta_bar != m_0;
  (c) under the finite law, enumerating (theta_0, z_1, eta_1): the filter's P_1 is the unconditional error covariance of
      theta_1 given y_1, and E[m_1] = Phi m_0 + (I - Phi) theta_bar;
  (d) on a T = 3 tree, the law of y_2 has covariance G (Phi P_0 Phi' + Q) G' + R and mean G (Phi m_0 + (I - Phi) theta_bar) + d
      (eta enters the tree).
Run: uv run python experiments/d16-harness/validate_m9.py
"""
import importlib.util
import itertools
import json
import multiprocessing as mp
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from harness_n import mn_model  # noqa: E402

_p = importlib.util.spec_from_file_location("presets", HERE.parent / "presets.py"); PR = importlib.util.module_from_spec(_p); _p.loader.exec_module(PR)
M9_ARGS = dict(phi=[0.8, 0.6], q=[4e-6, 2e-6], theta_bar=[0.012, 0.001])


def one_fund(regime, alpha_sd=None, V=None, fund_rate=None, etf_sell_mult=1.0, premium_sd_mult=1.0, **m9):
    P = PR.PRESETS[regime]; fr = P["fund_rate"] if fund_rate is None else fund_rate
    return mn_model(BA=[[1.0]], BE=[[1.0]], lam=P["premium"][0], alpha=P["alpha_mean"], premium_sd=P["premium_sd"][0] * premium_sd_mult,
                    sigma_f=P["factor_sd"][0], sigma_A=P["sigma_A"], alpha_sd=alpha_sd, alpha_revision_var=V, cE=[P["etf_fee"]], gamma=P["gamma"],
                    kp=[fr, P["etf_rate"]], km=[fr, P["etf_rate"] * etf_sell_mult], cap=[P["fund_cap"], np.inf], **m9)


def v054(c):
    P = PR.PRESETS[c["regime"]]; pa = P["alpha_sd"] ** 2; s2 = P["sigma_A"] ** 2
    M = one_fund(c["regime"], V=pa ** 2 / (pa + s2) * c["rv"], etf_sell_mult=c["sell"], phi=1.0, q=0.0)
    x0 = np.array(c["start"], float); D = M.solve(x0, c["cash"])
    mu0, S0 = M.moments(0, M.m0); xmy, _, _ = M.one_review(mu0, S0, x0, c["cash"])
    return float(np.max(np.abs(D["x"][0][0] - np.array(c["x_dyn"])))), float(np.max(np.abs(xmy - np.array(c["x_my"]))))


def v048(c):
    P = PR.PRESETS[c["regime"]]; un = c["unc"]
    M = one_fund(c["regime"], alpha_sd=P["alpha_sd"] * un, fund_rate=P["fund_rate"] * c["costmul"], premium_sd_mult=un, phi=1.0, q=0.0)
    D = M.solve(np.array(c["start"], float), c["cash"])
    return abs(D["value"] - c["dynamic"]["value"]), float(np.max(np.abs(D["x"][0][0] - np.array(c["dynamic"]["x0"]))))


def scalar_filter():
    """(b): SPEC M9's scalar recursion, with the factor read from the ETF's return (no ETF residual: f = (r^E + c^E)/b_E)."""
    worst = dict(m=0.0, P=0.0)
    for regime in PR.PRESETS:
        P = PR.PRESETS[regime]; M = one_fund(regime, alpha_sd=P["alpha_sd"], **M9_ARGS)
        phi = np.array(M9_ARGS["phi"]); q = np.array(M9_ARGS["q"]); tb = np.array(M9_ARGS["theta_bar"])
        sig2 = np.array([P["factor_sd"][0] ** 2, P["sigma_A"] ** 2]); p0 = np.diag(M.P0); k = p0 / (p0 + sig2)
        P1 = phi ** 2 * (1 - k) * p0 + q
        worst["P"] = max(worst["P"], float(np.max(np.abs(np.diag(M.P(1)) - P1))), float(np.max(np.abs(M.P(1) - np.diag(np.diag(M.P(1)))))))
        for nd in M.tree(2)[1]:
            y = nd["g"] - 1.0; f = (y[1] + M.cE[0]) / M.BE[0, 0]
            nu = np.array([f - M.m0[0], y[0] - M.BA[0, 0] * f - M.m0[1]])
            m1 = phi * (M.m0 + k * nu) + (1 - phi) * tb
            worst["m"] = max(worst["m"], float(np.max(np.abs(nd["m"] - m1))))
    return worst


def finite_law():
    """(c): enumerate (theta_0, z_1, eta_1) under the finite law."""
    P = PR.PRESETS["fixed-income-style"]; M = one_fund("fixed-income-style", alpha_sd=P["alpha_sd"], **M9_ARGS)
    E = np.zeros((2, 2)); Em = np.zeros(2); I = np.eye(2)
    for (th, pt), (z, pz), (e, pe) in itertools.product(zip(M.theta_atoms, M.theta_probs), zip(M.z_atoms, M.z_probs), zip(M.eta_atoms, M.eta_probs)):
        y = M.G @ th + M.d + M.L @ z; m1 = M.update(0, M.m0, y); th1 = M.Phi @ th + (I - M.Phi) @ M.theta_bar + e
        w = pt * pz * pe; E += w * np.outer(th1 - m1, th1 - m1); Em += w * m1
    return dict(P1=float(np.max(np.abs(E - M.P(1)))), mean_m1=float(np.max(np.abs(Em - (M.Phi @ M.m0 + (I - M.Phi) @ M.theta_bar)))))


def tree3():
    """(d): the T = 3 tree's law of y_2."""
    P = PR.PRESETS["equity-style"]; M = one_fund("equity-style", alpha_sd=P["alpha_sd"], **M9_ARGS)
    lev = M.tree(3); I = np.eye(2)
    ys = np.array([nd["g"] - 1.0 for nd in lev[2]]); pr = np.array([nd["prob"] for nd in lev[2]])
    mean = pr @ ys; cov = (ys - mean).T @ np.diag(pr) @ (ys - mean)
    mth = M.G @ (M.Phi @ M.m0 + (I - M.Phi) @ M.theta_bar) + M.d
    cth = M.G @ (M.Phi @ M.P0 @ M.Phi.T + M.Q) @ M.G.T + M.R
    return dict(prob_sum=float(abs(pr.sum() - 1)), mean=float(np.max(np.abs(mean - mth))), cov=float(np.max(np.abs(cov - cth))), nodes2=len(lev[2]))


def main():
    c48 = json.load(open(HERE.parent / "048" / "summary.json"))["cells"]; c54 = json.load(open(HERE.parent / "054" / "summary.json"))["cells"]
    with mp.Pool(8) as pool:
        r54 = pool.map(v054, c54); r48 = pool.map(v048, c48)
    out = dict(identity_vs054=dict(cells=len(c54), x_dyn=max(r[0] for r in r54), x_my=max(r[1] for r in r54)),
               identity_vs048=dict(cells=len(c48), value=max(r[0] for r in r48), x0=max(r[1] for r in r48)),
               scalar_filter=scalar_filter(), finite_law=finite_law(), tree3=tree3(), m9_args=M9_ARGS)
    json.dump(out, open(HERE / "validation_m9.json", "w"), indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
