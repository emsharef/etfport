"""Finite checks for claim 034 (D14: the plug-in loss as an explicit function of the inputs); not its proof.

Run: uv run python checks/034/check.py

 (i)  separated homogeneous instances: part 2's closed forms (exposure part, fund part) against claim 033's general
      moment recursion, on grids of starting holdings, prior means, residual-variance and factor-covariance errors
      (including an equity-style and a fixed-income-style point, illustrations only);
 (ii) part 3: the constant C against finite differences in epsilon; the costless and infinite-cost limits; the T = 1
      formula; non-monotonicity in lambda_A;
 (iii) part 4: fund coefficients unchanged by a factor-covariance error under spanning, changed without it.
"""
import importlib.util
import os
import sys

import numpy as np


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(os.path.dirname(__file__), "..", rel, "check.py"))
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod


_c30 = _load("check030", "030"); _c31 = _load("check031", "031"); _c33 = _load("check033", "033")
kalman_path, recursion = _c30.kalman_path, _c30.recursion
make = _c31.make
coefs, innovation_covs, exact_loss = _c33.coefs, _c33.innovation_covs, _c33.exact_loss
rng = np.random.default_rng(34)


# ---------- scalar fund block (part 2b, part 3) ----------
def scalar_coefs(lamA, gamma, sig2, p, T, rho=1.0):
    a, l = 0.0, 0.0; K = [0.0] * T; L = [0.0] * T; D = [0.0] * T
    for t in range(T - 1, -1, -1):
        d = lamA + gamma * (sig2 + p[t]) + rho * a
        K[t] = lamA / d; L[t] = (1 + rho * lamA * l) / d; D[t] = d
        a = lamA - lamA ** 2 / d; l = L[t]
    return np.array(K), np.array(L), np.array(D)


def scalar_derivs(lamA, gamma, sig2, p, T, rho=1.0):
    """Derivatives of (k_t, l_t) in the residual variance, part 3(i)'s recursion."""
    a, ap, l, lp = 0.0, 0.0, 0.0, 0.0; Kp = [0.0] * T; Lp = [0.0] * T
    for t in range(T - 1, -1, -1):
        d = lamA + gamma * (sig2 + p[t]) + rho * a; dp = gamma + rho * ap
        Kp[t] = -lamA * dp / d ** 2
        Lp[t] = (rho * lamA * lp * d - (1 + rho * lamA * l) * dp) / d ** 2
        a_new = lamA - lamA ** 2 / d; ap = lamA ** 2 * dp / d ** 2
        l = (1 + rho * lamA * l) / d; lp = Lp[t]; a = a_new
    return np.array(Kp), np.array(Lp)


def fund_loss_closed(lamA, gamma, sig2, sig2_hat, p, T, x0, alpha0, rho=1.0):
    """Part 2(b): closed-form fund loss for one fund."""
    K, L, D = scalar_coefs(lamA, gamma, sig2, p, T, rho)
    Kh, Lh, _ = scalar_coefs(lamA, gamma, sig2_hat, p, T, rho)
    dK, dL = Kh - K, Lh - L
    v = [p[u] - p[u + 1] for u in range(T)]
    loss = 0.0
    for t in range(T):
        # plug-in path coefficients: x_{t-1} = A x0 + sum_{s<t} B_s alpha_hat_s
        A = np.prod(Kh[:t]) if t > 0 else 1.0
        B = [np.prod(Kh[s + 1:t]) * Lh[s] for s in range(t)]  # s = 0..t-1
        mu = dK[t] * (A * x0 if t > 0 else x0) + (dK[t] * sum(B) + dL[t]) * alpha0 if t > 0 else dL[t] * alpha0 + dK[t] * x0
        var = 0.0
        for u in range(t):
            w = dK[t] * sum(B[s] for s in range(u + 1, t)) + dL[t]
            var += w ** 2 * v[u]
        loss += rho ** t * 0.5 * D[t] * (mu ** 2 + var)
    return loss


def fund_loss_general(lamA, gamma, sig2, sig2_hat, p, T, x0, alpha0, rho=1.0):
    """The same loss by claim 033's moment recursion specialized to the scalar case (independent implementation)."""
    K, L, D = scalar_coefs(lamA, gamma, sig2, p, T, rho)
    Kh, Lh, _ = scalar_coefs(lamA, gamma, sig2_hat, p, T, rho)
    # state z = (x_{t-1}, alpha_hat_t): mean and second moment
    mu = np.array([x0, alpha0]); S = np.outer(mu, mu); loss = 0.0
    for t in range(T):
        dvec = np.array([Kh[t] - K[t], Lh[t] - L[t]])
        loss += rho ** t * 0.5 * D[t] * (dvec @ S @ dvec)
        F = np.array([[Kh[t], Lh[t]], [0, 1]]); W = np.array([[0, 0], [0, p[t] - p[t + 1]]])
        S = F @ S @ F.T + W; mu = F @ mu
    return loss


def part2_and_3():
    gamma, sig2, T = 5.0, 0.02 ** 2, 8
    s2 = 0.0035 ** 2; p = [1 / (1 / s2 + t / sig2) for t in range(T + 1)]
    # (i) closed form vs general recursion on a grid, including illustrative regime points
    for lamA in [0.02, 0.1, 0.5]:
        for x0, alpha0, err in [(0.0, -0.0019, 0.3), (0.1, 0.0005, -0.3), (0.3, 0.002, 0.5), (0.05, -0.004, 0.1)]:
            a = fund_loss_closed(lamA, gamma, sig2, sig2 * (1 + err), p, T, x0, alpha0)
            b = fund_loss_general(lamA, gamma, sig2, sig2 * (1 + err), p, T, x0, alpha0)
            assert abs(a - b) < 1e-14 + 1e-9 * abs(b), (lamA, x0, alpha0, err, a, b)
    print("  part 2(b): closed-form fund loss equals the general moment recursion on the grid")
    # (ii) constant C vs finite differences
    lamA, x0, alpha0 = 0.1, 0.1, 0.002
    Kp, Lp = scalar_derivs(lamA, gamma, sig2, p, T)
    K, L, D = scalar_coefs(lamA, gamma, sig2, p, T)
    mu = np.array([x0, alpha0]); S = np.outer(mu, mu); C = 0.0
    for t in range(T):
        dv = np.array([Kp[t], Lp[t]]); C += 0.5 * D[t] * (dv @ S @ dv)
        F = np.array([[K[t], L[t]], [0, 1]]); W = np.array([[0, 0], [0, p[t] - p[t + 1]]]); S = F @ S @ F.T + W
    eps = 1e-6 * sig2
    Lfd = fund_loss_general(lamA, gamma, sig2, sig2 + eps, p, T, x0, alpha0) / eps ** 2
    assert abs(Lfd - C) < 1e-3 * C, (Lfd, C)
    print(f"  part 3(i): C = {C:.6e} equals the finite-difference second-order coefficient {Lfd:.6e}")
    # costless limit
    r = [gamma * (sig2 + p[t]) for t in range(T)]; rt = [gamma * (1.3 * sig2 + p[t]) for t in range(T)]
    myopic = sum(0.5 * r[t] * (1 / rt[t] - 1 / r[t]) ** 2 * (alpha0 ** 2 + p[0] - p[t]) for t in range(T))
    small = fund_loss_general(1e-9, gamma, sig2, 1.3 * sig2, p, T, x0, alpha0)
    assert abs(small - myopic) < 1e-6 * myopic, (small, myopic)
    big5 = fund_loss_general(1e5, gamma, sig2, 1.3 * sig2, p, T, x0, alpha0)
    big6 = fund_loss_general(1e6, gamma, sig2, 1.3 * sig2, p, T, x0, alpha0)
    assert big6 < 1e-6 * myopic and 8 < big5 / big6 < 12, (big5, big6)   # decays like 1/lambda_A
    print(f"  part 3(ii)-(iii): costless limit {small:.4e} = myopic {myopic:.4e}; infinite-cost limit: loss {big5:.2e} at 1e5, {big6:.2e} at 1e6 (order 1/lambda_A)")
    # T = 1 formula and non-monotonicity in lambda_A
    p1 = p[:2]; r0 = gamma * (sig2 + p1[0]); r0t = gamma * (1.3 * sig2 + p1[0])
    vals = []
    for lam in [0.001, 0.01, 0.05, 0.2, 1.0, 10.0]:
        t1 = fund_loss_general(lam, gamma, sig2, 1.3 * sig2, p1, 1, x0, alpha0)
        f = 0.5 * (lam + r0) * ((lam * x0 + alpha0) * (1 / (lam + r0t) - 1 / (lam + r0))) ** 2
        assert abs(t1 - f) < 1e-14 + 1e-9 * f, (lam, t1, f)
        vals.append(fund_loss_general(lam, gamma, sig2, 1.3 * sig2, p1, 1, x0, 0.0))   # alpha_hat_0 = 0: rises then falls
    assert max(vals) > vals[0] and max(vals) > vals[-1], vals
    print(f"  part 3(iv): T = 1 formula exact; with alpha_hat_0 = 0 the loss over lambda_A rises then falls: {[f'{v:.2e}' for v in vals]}")


def part2a_exposure():
    """Exposure part against claim 033's general machinery on a separated instance with a factor-covariance error."""
    I = make((3, 2, 2), 5.0, 6)  # separated: ETF cost, residual, fee zero; B^E invertible
    K, N, T = I["K"], I["N"], I["T"]
    Ps, Ks = kalman_path(I)
    Sig_true = [I["G"] @ Ps[t] @ I["G"].T + I["Sig_r"] for t in range(T)]
    V = innovation_covs(I, Ps, Ks)
    E = rng.standard_normal((K, K)); E = 0.3 * (E @ E.T) / K * np.trace(I["Sig_f"]) / K
    Sf_hat = I["Sig_f"] + E
    Sig_r_hat = I["B"] @ Sf_hat @ I["B"].T + np.block([[I["Sig_A"], np.zeros((N, 2))], [np.zeros((2, N)), I["Sig_E"]]])
    Sig_est = [I["G"] @ Ps[t] @ I["G"].T + Sig_r_hat for t in range(T)]
    Rt, Rp = coefs(I, Sig_true), coefs(I, Sig_est)
    x0 = 0.1 * np.ones(N + 2); m0 = I["m0"]
    general = exact_loss(I, Sig_true, Rt, Rp, x0, m0, V)
    # closed form: exposure part only (fund coefficients unchanged under spanning)
    lam0 = m0[:K]; closed = 0.0
    for t in range(T):
        SL = I["Sig_f"] + Ps[t][:K, :K]; SLh = Sf_hat + Ps[t][:K, :K]
        Dl = (np.linalg.inv(SLh) - np.linalg.inv(SL)) @ SL @ (np.linalg.inv(SLh) - np.linalg.inv(SL))
        closed += (1 / (2 * I["gamma"])) * np.trace(Dl @ (np.outer(lam0, lam0) + Ps[0][:K, :K] - Ps[t][:K, :K]))
    assert abs(general - closed) < 1e-12 + 1e-8 * closed, (general, closed)
    # part 4: fund coefficients unchanged under spanning
    for t in range(T):
        assert np.allclose(Rt[t]["K"][:N, :N], Rp[t]["K"][:N, :N], atol=1e-12) and np.allclose(Rt[t]["L"][:N, K:], Rp[t]["L"][:N, K:], atol=1e-12)
    print(f"  part 2(a) and 4: exposure-part closed form {closed:.4e} equals the general loss {general:.4e}; fund coefficients untouched by the factor error under spanning")
    # missing direction: the factor error changes the fund coefficients and adds fund loss
    J = make((2, 1, 2), 5.0, 6)
    Ps, Ks = kalman_path(J); N = J["N"]; K = J["K"]
    Sig_true = [J["G"] @ Ps[t] @ J["G"].T + J["Sig_r"] for t in range(J["T"])]
    Sf_hat = J["Sig_f"] + 0.3 * np.diag(np.diag(J["Sig_f"]))
    Sig_r_hat = J["B"] @ Sf_hat @ J["B"].T + np.block([[J["Sig_A"], np.zeros((N, 1))], [np.zeros((1, N)), J["Sig_E"]]])
    Sig_est = [J["G"] @ Ps[t] @ J["G"].T + Sig_r_hat for t in range(J["T"])]
    Rt, Rp = coefs(J, Sig_true), coefs(J, Sig_est)
    changed = max(np.abs(Rt[t]["K"][:N, :N] - Rp[t]["K"][:N, :N]).max() for t in range(J["T"]))
    assert changed > 1e-6, changed
    print(f"  part 4: without spanning the factor-covariance error changes the fund coefficients (max change {changed:.3e})")


def main():
    part2_and_3()
    part2a_exposure()
    print("checks/034: all checks passed")


if __name__ == "__main__":
    main()
    sys.exit(0)
