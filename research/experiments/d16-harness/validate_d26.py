"""Validation of harness_n's D26 extensions (preparation; PM's note 2026-10-01-d26-start). No findings.
  (a) observe_factor = True (M9's observation y = (f, r^A, r^E)) equals the returns-only observation where the ETFs span
      the factors without residuals: experiment 054's cells (dynamic roots) and experiment 056's registered cells;
  (b) with ETF residuals (N = 3, M = 2, K = 2, observe_factor), the filter decouples into M9's scalar recursions per
      coordinate (lambda_k from f_k, alpha_i from r^A_i - B^A_i f), with Phi and Q, and P_t stays diagonal;
  (c) the axis law: theta's and z's atoms have the stated mean and covariance, the tree's law of y_1 has mean H m_0 + d and
      covariance H P_0 H' + R, and gross returns are positive on the support (both laws);
  (d) budget_t = {0} (D26's policy 2): tomorrow's node decisions equal the unbudgeted one-review solves from the plan's
      marked root holdings.
Run: uv run python experiments/d16-harness/validate_d26.py
"""
import importlib.util
import json
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from harness_n import mn_model, axis_law  # noqa: E402

_p = importlib.util.spec_from_file_location("presets", HERE.parent / "presets.py"); PR = importlib.util.module_from_spec(_p); _p.loader.exec_module(PR)


def a_observe():
    worst = 0.0
    for c in json.load(open(HERE.parent / "054" / "summary.json"))["cells"][::9]:
        P = PR.PRESETS[c["regime"]]; pa = P["alpha_sd"] ** 2; s2 = P["sigma_A"] ** 2
        kw = dict(BA=[[1.0]], BE=[[1.0]], lam=P["premium"][0], alpha=P["alpha_mean"], premium_sd=P["premium_sd"][0], sigma_f=P["factor_sd"][0], sigma_A=P["sigma_A"],
                  alpha_revision_var=pa ** 2 / (pa + s2) * c["rv"], cE=[P["etf_fee"]], gamma=P["gamma"], kp=[P["fund_rate"], P["etf_rate"]],
                  km=[P["fund_rate"], P["etf_rate"] * c["sell"]], cap=[P["fund_cap"], np.inf])
        x0 = np.array(c["start"], float)
        Dy = mn_model(observe_factor=True, **kw).solve(x0, c["cash"])
        worst = max(worst, float(np.max(np.abs(Dy["x"][0][0] - np.array(c["x_dyn"])))))
    w56 = 0.0
    _s = importlib.util.spec_from_file_location("r56", HERE.parent / "056" / "run.py"); R56 = importlib.util.module_from_spec(_s); _s.loader.exec_module(R56)
    for c in [c for c in json.load(open(HERE.parent / "056" / "summary.json"))["cells"] if c["regime"] != "supplement"][::4]:
        M = R56.model(c["regime"], c["setting"], c["mult"]); M2 = mn_model(observe_factor=True, **_kwargs56(c))
        D = M2.solve(np.array(c["x0"]), c["cash"]); w56 = max(w56, float(np.max(np.abs(D["x"][0][0] - np.array(c["x_dyn"])))))
    return dict(vs054_x_dyn=worst, vs056_x_dyn=w56)


def _kwargs56(c):
    P = PR.PRESETS[c["regime"]]; pa = P["alpha_sd"] ** 2; s2 = P["sigma_A"] ** 2; fr = P["fund_rate"]
    V = pa ** 2 / (pa + s2) * (c["mult"] if c["setting"] == "revision_var" else 1.0)
    return dict(BA=[[1.0, 0.3], [0.6, 0.8]], BE=[[1.0, 0.0], [0.5, 1.0]], lam=list(P["premium"]), alpha=[P["alpha_mean"], P["alpha_mean"] / 2],
                premium_sd=list(P["premium_sd"]), sigma_f=list(P["factor_sd"]), sigma_A=P["sigma_A"], alpha_revision_var=V, cE=[0.0, 0.0], gamma=P["gamma"],
                kp=[fr, 1.5 * fr, 0.0, 0.0], km=[fr, 1.5 * fr, 0.0, 0.0], cap=[P["fund_cap"], P["fund_cap"], np.inf, np.inf])


def menu(law="product", **m9):
    return mn_model(BA=[[1.0, 0.2], [0.8, 0.6], [0.5, 1.0]], BE=[[1.0, 0.0], [0.3, 1.0]], lam=[0.015, 0.005], alpha=[0.002, 0.001, 0.0],
                    premium_sd=[0.005, 0.005], sigma_f=[0.08, 0.04], sigma_A=[0.02, 0.025, 0.03], alpha_sd=[0.0035, 0.004, 0.003], sigma_E=[0.002, 0.003],
                    cE=[0.0003, 0.0005], gamma=5.0, kp=[0.005, 0.006, 0.004, 0.0002, 0.0003], km=[0.005, 0.006, 0.004, 0.0002, 0.0003],
                    cap=[0.25, 0.25, 0.25, np.inf, np.inf], law=law, observe_factor=True, **m9)


def b_decouple():
    m9 = dict(phi=[0.9, 1.0, 0.5, 0.8, 1.0], q=[1e-6, 0.0, 1e-7, 0.0, 2e-7], theta_bar=[0.012, 0.005, 0.004, 0.0, -0.001])
    M = menu(**m9); phi = np.array(m9["phi"]); q = np.array(m9["q"]); tb = np.array(m9["theta_bar"])
    noise = np.concatenate([np.diag(M.Sz)[:2], np.diag(M.Sz)[2:5]])
    p = np.diag(M.P0).copy(); worstP = offd = 0.0
    for t in range(4):
        Pt = M.P(t); worstP = max(worstP, float(np.max(np.abs(np.diag(Pt) - p)))); offd = max(offd, float(np.max(np.abs(Pt - np.diag(np.diag(Pt))))))
        k = p / (p + noise); p = phi ** 2 * (1 - k) * p + q
    k0 = np.diag(M.P0) / (np.diag(M.P0) + noise); worstm = 0.0
    for nd in M.tree(2)[1]:
        r = nd["g"] - 1.0; f = np.array(nd["key"][:2])
        nu = np.concatenate([f - M.m0[:2], r[:3] - M.BA @ f - M.m0[2:]])
        worstm = max(worstm, float(np.max(np.abs(nd["m"] - (phi * (M.m0 + k0 * nu) + (1 - phi) * tb)))))
    return dict(P_diag_err=worstP, P_offdiag=offd, m1_err=worstm)


def c_laws():
    out = {}
    for law in ("product", "axis"):
        M = menu(law=law, phi=[0.9, 1.0, 0.5, 0.8, 1.0], q=[1e-6, 0.0, 1e-7, 0.0, 2e-7])
        th, pt = np.array(M.theta_atoms), np.array(M.theta_probs); za, pz = np.array(M.z_atoms), np.array(M.z_probs)
        lev = M.tree(2)[1]; ys = np.array([np.array(nd["key"]) for nd in lev]); pr = np.array([nd["prob"] for nd in lev])
        mean = pr @ ys; cov = (ys - mean).T @ np.diag(pr) @ (ys - mean)
        out[law] = dict(theta_atoms=len(th), z_atoms=len(za), states=len(lev),
                        theta_cov=float(np.max(np.abs((th - M.m0).T @ np.diag(pt) @ (th - M.m0) - M.P0))), z_cov_mean=float(max(np.max(np.abs(pz @ za)), np.max(np.abs(za.T @ np.diag(pz) @ za - M.Sz)))),
                        y_mean=float(np.max(np.abs(mean - (M.Ho @ M.m0 + M.do)))), y_cov=float(np.max(np.abs(cov - (M.Ho @ M.P0 @ M.Ho.T + M.Ro)))),
                        min_gross=float(min(nd["g"].min() for nd in lev)))
    return out


def d_relaxed():
    M = menu(phi=[0.9, 1.0, 0.5, 0.8, 1.0], q=[1e-6, 0.0, 1e-7, 0.0, 2e-7]); x0 = np.array([0.1, 0.05, 0.0, 0.3, 0.1])
    D = M.solve(x0, 0.02, budget_t={0}); xr = D["x"][0][0]; hr = D["h"][0][0]; worst = 0.0; neg = 0
    for k, nd in enumerate(D["levels"][1]):
        mu, S = M.moments(1, nd["m"]); x1, _, h1 = M.one_review(mu, S, xr * nd["g"], hr, budget=False)
        worst = max(worst, float(np.max(np.abs(x1 - D["x"][1][k])))); neg += int(h1 < -1e-9)
    return dict(node_err=worst, states=len(D["levels"][1]), states_with_negative_cash=neg, root_cash=hr)


def main():
    out = dict(a_observe_factor=a_observe(), b_decoupled_filter=b_decouple(), c_laws=c_laws(), d_relaxed_tomorrow=d_relaxed())
    json.dump(out, open(HERE / "validation_d26.json", "w"), indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
