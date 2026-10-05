"""Finite checks for claim 036 (D15 (a): when anticipating learning or mean reversion changes today's trade); not its proof.

Run: uv run python checks/036/check.py

Scalar fund blocks over grids of inputs:
 part 1: aim_t = L_t aim^S_t with 1 <= L_t <= 1/(1 - kappa_t), strict inside, the threshold kappa_t > theta/(1+theta);
 part 2: g_t <= g^S_t with the stated bound, and the trade identity and bound;
 part 3: the aim under an AR(1) alpha computed by the affine recursion (independently of the weight formula) equals the
         weight formula; M_t(phi) within its bounds, nondecreasing in phi, and -> 1 as lambda_A -> 0.
Inputs are illustrative (rule 22).
"""
import itertools
import sys

import numpy as np

rng = np.random.default_rng(36)


def recursion(lamA, gamma, sig2, p, T, rho=1.0, phi=1.0, abar=0.0):
    """Scalar fund block with an AR(1) alpha (phi = 1: martingale). Returns per-t (d, a, g, k, q, c) with the aim's
    affine coefficients: aim_t = Q_t alpha_hat_t + c_t; policy x_t = k_t x_{t-1} + q_t alpha_hat_t + cst_t."""
    a = 0.0; C = 0.0; c = 0.0
    out = [None] * T
    for t in range(T - 1, -1, -1):
        r = gamma * (sig2 + p[t]); d = lamA + r + rho * a
        # value-function linear coefficients with E_t m_{t+1} = phi m_t + (1 - phi) abar
        v_lin = 1.0 + rho * C * phi; v_cst = rho * (C * (1 - phi) * abar + c)
        Q = v_lin / (r + rho * a); Qc = v_cst / (r + rho * a)        # aim = Q alpha_hat + Qc
        k = lamA / d; q = v_lin / d; cst = v_cst / d
        out[t] = dict(d=d, anext=a, g=1 - lamA / d, k=k, q=q, cst=cst, Q=Q, Qc=Qc, r=r)
        a_new = lamA - lamA ** 2 / d
        C = lamA * v_lin / d; c = lamA * v_cst / d; a = a_new
    return out


def weights(lamA, gamma, sig2, p, T, t, rho=1.0):
    R = recursion(lamA, gamma, sig2, p, T, rho)
    w = []
    for s in range(t, T):
        prod = 1.0
        for u in range(t, s):
            prod *= rho * R[u]["anext"] / (R[u]["d"] - lamA)
        w.append(prod * R[s]["r"] / (R[s]["d"] - lamA))
    return np.array(w), R


def main():
    sig2 = 0.02 ** 2
    for s2_ratio, lamA, gamma, T in itertools.product([0.03, 0.3, 1.0], [0.01, 0.1, 1.0], [2.0, 10.0], [4, 12]):
        s2 = s2_ratio * sig2; p = [1 / (1 / s2 + t / sig2) for t in range(T + 1)]
        for t in [0, T // 2, T - 1]:
            w, R = weights(lamA, gamma, sig2, p, T, t)
            assert abs(w.sum() - 1) < 1e-12 and w.min() >= 0
            ell = float(np.sum(w * sig2 / (sig2 + np.array(p[t:T]))))
            L = ell * (sig2 + p[t]) / sig2; kap = p[t] / (sig2 + p[t])
            # part 1: aim from the recursion equals L * aim^S
            aim_over_alpha = R[t]["Q"]; aimS = 1 / (gamma * (sig2 + p[t]))
            assert abs(aim_over_alpha - L * aimS) < 1e-12 * aimS, (aim_over_alpha, L * aimS)
            assert 1 - 1e-12 <= L <= 1 / (1 - kap) + 1e-12
            if t < T - 1:
                assert L > 1 + 1e-15 and L < 1 / (1 - kap) - 1e-15
            else:
                assert abs(L - 1) < 1e-12
            # part 2: rates
            pS = [p[t]] * (T + 1)
            RS = recursion(lamA, gamma, sig2, pS, T)        # static-belief (frozen at p_t) from t
            gS = RS[t]["g"]; g = R[t]["g"]
            pinf = [0.0] * (T + 1); Rinf = recursion(lamA, gamma, sig2, pinf, T); ginf = Rinf[t]["g"]
            assert g <= gS + 1e-12 and gS - g <= gS - ginf + 1e-12, (g, gS, ginf)
            # trade identity and bound at random state
            x, ah = rng.uniform(-0.5, 0.5), rng.uniform(-0.01, 0.01)
            u = g * (L * aimS * ah - x); uS = gS * (aimS * ah - x)
            ident = (g - gS) * (aimS * ah - x) + g * (L - 1) * aimS * ah
            assert abs((u - uS) - ident) < 1e-14
            assert abs(u - uS) <= (gS - ginf) * abs(aimS * ah - x) + g * kap / (1 - kap) * abs(aimS * ah) + 1e-14
        # part 3: mean reversion
        t = 0; abar = -0.001
        w, R = weights(lamA, gamma, sig2, p, T, t)
        wt = w * sig2 / (sig2 + np.array(p[t:T])); ell = wt.sum(); wt = wt / ell
        prev = -1.0
        for phi in [0.0, 0.3, 0.6, 0.9, 1.0]:
            Rp = recursion(lamA, gamma, sig2, p, T, phi=phi, abar=abar)
            M = float(np.sum(wt * phi ** np.arange(T - t)))
            # aim = ell abar/(gamma sig2) + M ell (alpha_hat - abar)/(gamma sig2): compare with the recursion's affine aim
            for ah in [-0.005, 0.002]:
                aim_rec = Rp[t]["Q"] * ah + Rp[t]["Qc"]
                aim_formula = ell * abar / (gamma * sig2) + M * ell * (ah - abar) / (gamma * sig2)
                assert abs(aim_rec - aim_formula) < 1e-12 * (abs(aim_formula) + 1e-9), (phi, aim_rec, aim_formula)
            assert wt[0] + (1 - wt[0]) * phi ** (T - 1 - t) - 1e-12 <= M <= 1 + 1e-12
            assert M >= prev - 1e-12; prev = M
    # zero-cost limit of M_t(phi)
    s2 = 0.3 * sig2; T = 8; p = [1 / (1 / s2 + t / sig2) for t in range(T + 1)]
    for phi in [0.0, 0.5]:
        w, R = weights(1e-9, 5.0, sig2, p, T, 0); wt = w * sig2 / (sig2 + np.array(p[:T])); wt /= wt.sum()
        M = float(np.sum(wt * phi ** np.arange(T)))
        assert M > 1 - 1e-6, (phi, M)
    # illustrations (rule 22): equity-style and fixed-income-style points, printed only
    for name, s2r, lamA, gamma in [("equity-style", 0.03, 0.1, 5.0), ("fixed-income-style", 0.3, 0.5, 5.0)]:
        s2 = s2r * sig2; T = 12; p = [1 / (1 / s2 + t / sig2) for t in range(T + 1)]
        w, R = weights(lamA, gamma, sig2, p, T, 0); ell = float(np.sum(w * sig2 / (sig2 + np.array(p[:T]))))
        L = ell * (sig2 + p[0]) / sig2; kap = p[0] / (sig2 + p[0])
        print(f"  {name} (illustration): Kalman gain {kap:.3f}, learning factor {L:.4f} (bound {1 / (1 - kap):.4f}), myopic weight w_00 {w[0]:.3f}")
    print("  parts 1-3 verified on the grid (36 blocks x 3 reviews; 5 persistence levels)")
    print("checks/036: all checks passed")


if __name__ == "__main__":
    main()
    sys.exit(0)
