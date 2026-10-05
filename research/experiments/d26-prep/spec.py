"""D26 preparation: the integrated example's input specification (draft; the registration fixes the design).
Every number here is an assumed input (rule 22), labelled in SPEC.md. Preparation code, no findings.

The example: K = 2 factors, M = 2 ETFs, N = 3 funds, cash; M9 (model/SPEC.md) with the observation y = (f, r^A, r^E).
  factors   premia lambda = (0.015, 0.005) per quarter, factor SDs (0.08, 0.04), prior premium SDs (0.005, 0.005)
  ETFs      E1 broad (1.0, 0.0), E2 tilted (0.3, 1.0); fees c^E = (0.0003, 0.0005) per quarter; tracking residual SDs (0.002, 0.003)
  funds     F1 (1.0, 0.2), F2 (0.8, 0.6), F3 (0.5, 1.0); residual SDs (0.02, 0.025, 0.03); alpha means the regime preset's
            alpha_mean + (0, +0.002, -0.001); alpha prior SDs the preset's alpha_sd (scaled by the revision-uncertainty knob)
  costs     the regime preset's rates: funds fund_rate x (1, 1.5, 0.75) on both sides, ETFs etf_rate x (1, 1.5)
  limits    funds capped at 0.25 each, ETFs uncapped, no shorting; gamma = 5, beta = 1
  M9        Phi = diag(phi_lambda x 2, phi_alpha x 3), Q = diag(q_lambda x 2, q_alpha x 3), theta_bar = m_0 + the predictable shift
Knobs (the registration picks the levels):
  pred_alpha   theta_bar_alpha - m_0,alpha (with phi_alpha < 1): a predictable alpha move
  pred_lambda  theta_bar_lambda_1 - m_0,lambda_1 (with phi_lambda < 1): a predictable premium move
  unc          the alpha prior variance's multiplier (the revision uncertainty), separately from the predictable move
  q_mult       the state noise's multiplier
  regime       equity-style (cheap ETFs, mostly negative net alpha) or fixed-income-style (costlier ETFs, positive net alpha)
  start        construction from cash, or rebalancing an existing portfolio; with the initial cash
  fund_mult, etf_mult   the relative costs within a regime
  negative     fund 3 loads -0.6 on the second factor: negative covariances, outside the funding bounds' scope
"""
import importlib.util
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "d16-harness"))
from harness_n import mn_model  # noqa: E402

_p = importlib.util.spec_from_file_location("presets", HERE.parent / "presets.py"); PR = importlib.util.module_from_spec(_p); _p.loader.exec_module(PR)

BE = [[1.0, 0.0], [0.3, 1.0]]
BA = [[1.0, 0.2], [0.8, 0.6], [0.5, 1.0]]
STARTS = {"cash": (np.zeros(5), 1.0), "rebalance": (np.array([0.10, 0.10, 0.05, 0.40, 0.20]), 0.15),
          "rebalance-tight": (np.array([0.10, 0.10, 0.05, 0.40, 0.20]), 0.02)}


BA_NEG = [[1.0, 0.2], [0.8, 0.6], [0.5, -0.6]]      # out of the funding bounds' scope: fund 3 short the second factor


def build(regime="equity-style", pred_alpha=0.0, pred_lambda=0.0, phi_alpha=0.5, phi_lambda=0.7, unc=1.0, q_alpha=0.0, q_lambda=0.0, law="product",
          fund_mult=1.0, etf_mult=1.0, negative=False):
    P = PR.PRESETS[regime]
    alpha = P["alpha_mean"] + np.array([0.0, 0.002, -0.001]); lam = np.array([0.015, 0.005])
    m0 = np.concatenate([lam, alpha])
    tb = m0 + np.concatenate([[pred_lambda, 0.0], np.full(3, pred_alpha)])
    phi = np.concatenate([np.full(2, phi_lambda if pred_lambda or q_lambda else 1.0), np.full(3, phi_alpha if pred_alpha or q_alpha else 1.0)])
    fr = P["fund_rate"] * fund_mult * np.array([1.0, 1.5, 0.75]); er = P["etf_rate"] * etf_mult * np.array([1.0, 1.5])
    return mn_model(BA=BA_NEG if negative else BA, BE=BE, lam=lam, alpha=alpha, premium_sd=[0.005, 0.005], sigma_f=[0.08, 0.04], sigma_A=[0.02, 0.025, 0.03],
                    alpha_sd=P["alpha_sd"] * np.sqrt(unc), sigma_E=[0.002, 0.003], cE=[0.0003, 0.0005], gamma=5.0, beta=1.0,
                    kp=np.concatenate([fr, er]), km=np.concatenate([fr, er]), cap=[0.25, 0.25, 0.25, np.inf, np.inf],
                    phi=phi, q=np.concatenate([np.full(2, q_lambda), np.full(3, q_alpha)]), theta_bar=tb, law=law, observe_factor=True)


def entrywise_nonnegative(M, tol=0.0):
    """The funding bounds' scope (claims 049, 113, 115): Sigma_0 and Sigma_1 entrywise nonnegative."""
    return bool(min(M.moments(0, M.m0)[1].min(), M.moments(1, M.m0)[1].min()) >= -tol)
