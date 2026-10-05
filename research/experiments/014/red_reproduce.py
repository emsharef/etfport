"""Red's reproduction of experiment 014, written from the registered Design without reading run.py.

- Reuses red's experiment 013 reproduction: geometry, laws, rule (a)'s exact two-point critical values
  and the (b0) boundary.
- (b1) and (c) implement howard2021time Theorem 4 with the polynomial stitched boundary (10), read from
  the registered text: eta = 2, m = 1, s = 1.4, linear-term scale c = 2 as registered, l_0 = 1, and
  alpha = eta_err/4 per sequence.
- (b2) implements maurer2009empirical Theorem 4 at delta = eta_err/2 per face.
- The stress laws (Second question) are built from the Design's description.
Red's own Monte Carlo, with seeds independent of the analyst's.

Usage: uv run python experiments/014/red_reproduce.py
"""
import math
import sys
from pathlib import Path

import numpy as np
from scipy.special import zeta

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "013"))
import red_reproduce as E13  # noqa: E402  (red's experiment 013 reproduction)

LAM, SD, D, SIG, B = E13.LAM, E13.SD, E13.D, E13.SIG, E13.B
R, NMAX, ETAS = 20000, 160, (0.05, 0.25)
ns = np.arange(4, NMAX + 1)
K1, K2 = (2 ** 0.25 + 2 ** -0.25) / math.sqrt(2), (math.sqrt(2) + 1) / 2


def stitched(v, alpha, s=1.4, eta=2.0, m=1.0, c=2.0):
    v = np.maximum(v, m)
    ell = s * np.log(np.log(eta * v / m)) + math.log(zeta(s) / (alpha * math.log(eta) ** s))
    return K1 * np.sqrt(v * ell) + c * K2 * ell


def eb_halfwidth(Z, alpha):
    """Theorem 4 radius u(V_t)/t for [0,1] data Z (R x T), with the running-mean predictor (Z_hat_1 = 1/2)."""
    T = Z.shape[1]
    csum = np.cumsum(Z, axis=1)
    pred = np.concatenate([np.full((Z.shape[0], 1), 0.5), csum[:, :-1] / np.arange(1, T)[None, :]], axis=1)
    V = np.cumsum((Z - pred) ** 2, axis=1)
    return stitched(V, alpha) / np.arange(1, T + 1)[None, :], csum / np.arange(1, T + 1)[None, :]


def main():
    fails = []
    T = {eta: np.array([E13.t_exact(int(n), eta) for n in ns]) for eta in ETAS}
    # Known ranges (Design): m_0 in [-0.15, 0.15], m_1 in [-0.25, 0.25]; u, lambda_2 likewise.
    rng_face = [(-0.15 - B[0], 0.15 + B[0]), (-0.25 - B[1], 0.25 + B[1])]
    rng_u = (-0.15 - 4 * (SD[0] + SD[2]), 0.15 + 4 * (SD[0] + SD[2]))
    rng_l2 = (-0.10 - 4 * SD[1], 0.10 + 4 * SD[1])
    rng = np.random.default_rng(1414)
    laws = E13.laws(rng)
    print("### Main question (red's MC, R = 20,000 per law)\n")
    for name, (vals, probs) in laws.items():
        U = rng.choice(vals, size=(R, NMAX, 3), p=probs)
        X = LAM[None, None, [0, 1, 1]] * 0 + U * SD[None, None, :]      # errors only; means added per gap
        err = [X @ (D[j]) for j in range(2)]                             # d_j' J U, shape (R, T)
        eu, el2 = X[:, :, 0] + X[:, :, 2], X[:, :, 1]
        for gap in (0, 25, 100):
            g = gap * 1e-4
            alpha_true = g - LAM[0] + LAM[1]
            m = [LAM[0] + alpha_true, LAM[0] - LAM[1] + alpha_true]
            for eta in ETAS:
                out = {}
                # (b1): per-face EB CS on rescaled observations of d_j'X
                cert_b1 = np.ones((R, NMAX), bool)
                hw1 = []
                for j in range(2):
                    lo, hi = rng_face[j]
                    Z = (m[j] + err[j] - lo) / (hi - lo)
                    hw, mean = eb_halfwidth(Z, eta / 4)
                    lower = lo + (hi - lo) * (mean - hw)
                    cert_b1 &= lower > 0
                    hw1.append(np.median(hw[:, -1]) * (hi - lo) * 1e4)
                # (c): lower bound on u minus max(0, upper bound on lambda_2)
                Zu = (m[0] + eu - rng_u[0]) / (rng_u[1] - rng_u[0])
                Zl = (LAM[1] + el2 - rng_l2[0]) / (rng_l2[1] - rng_l2[0])
                hu, mu_ = eb_halfwidth(Zu, eta / 4)
                hl, ml_ = eb_halfwidth(Zl, eta / 4)
                u_lo = rng_u[0] + (rng_u[1] - rng_u[0]) * (mu_ - hu)
                l_hi = rng_l2[0] + (rng_l2[1] - rng_l2[0]) * (ml_ + hl)
                cert_c = (u_lo - np.maximum(0, l_hi)) > 0
                # (b2): Maurer-Pontil at n = 40, 80, 160 (one-sided, delta = eta/2 per face)
                cert_b2 = {}
                for n in (40, 80, 160):
                    ok = np.ones(R, bool)
                    for j in range(2):
                        lo, hi = rng_face[j]
                        Z = (m[j] + err[j][:, :n] - lo) / (hi - lo)
                        Vn = Z.var(axis=1, ddof=1)
                        w = np.sqrt(2 * Vn * math.log(2 / (eta / 2)) / n) + 7 * math.log(2 / (eta / 2)) / (3 * (n - 1))
                        ok &= lo + (hi - lo) * (Z.mean(1) - w) > 0
                    cert_b2[n] = ok.mean()
                # (a): known-law gate, exact two-point critical values
                me = [m[j] + np.cumsum(err[j], 1)[:, 3:] / ns[None, :] for j in range(2)]
                cert_a = np.minimum(me[0] - np.sqrt(T[eta] / ns) * SIG[0], me[1] - np.sqrt(T[eta] / ns) * SIG[1]) > 0
                law_free = [cert_b1.any(), cert_c.any(), any(v > 0 for v in cert_b2.values())]
                if any(law_free):
                    fails.append(f"a law-free rule certified under {name}, gap {gap}, eta {eta}")
                if name.startswith("lattice") and gap == 0:
                    print(f"  lattice normal, eta={eta}: EB CS (b1) median 40-y half-widths {np.round(hw1, 0)} bp")
                if gap == 0:
                    print(f"  {name:32s} eta={eta}: (a) single 10/20/40 y {cert_a[:, 36].mean():.4f} {cert_a[:, 76].mean():.4f} "
                          f"{cert_a[:, 156].mean():.4f}, ever {cert_a.any(1).mean():.4f}; law-free (b1, c, b2) any certification: "
                          f"{law_free}")
    # Second question: rule (a) at the null under the stress laws.
    print("\n### Second question: (a) at the null under stress laws (red's MC, R = 20,000)\n")
    stress = {}
    for a in (2, 3, 5, 8):
        stress[f"three-point a={a}"] = (np.array([-a, 0.0, a]), np.array([1 / (2 * a * a), 1 - 1 / a ** 2, 1 / (2 * a * a)]))
    for p in (0.2, 0.05, 0.01, 0.002):
        v = np.array([-math.sqrt(p / (1 - p)), math.sqrt((1 - p) / p)])
        stress[f"skew-right p={p}"] = (v, np.array([1 - p, p]))
        stress[f"skew-left p={p}"] = (-v, np.array([1 - p, p]))
    rng2 = np.random.default_rng(2114)
    first = None
    for name, (vals, probs) in stress.items():
        assert abs(probs @ vals) < 1e-12 and abs(probs @ vals ** 2 - 1) < 1e-12
        U = rng2.choice(vals, size=(R, NMAX, 3), p=probs)
        X = U * SD[None, None, :]
        err = [X @ D[j] for j in range(2)]
        alpha0 = -LAM[0] + LAM[1]
        m = [LAM[0] + alpha0, LAM[0] - LAM[1] + alpha0]
        me = [m[j] + np.cumsum(err[j], 1)[:, 3:] / ns[None, :] for j in range(2)]
        for eta in ETAS:
            cert = np.minimum(me[0] - np.sqrt(T[eta] / ns) * SIG[0], me[1] - np.sqrt(T[eta] / ns) * SIG[1]) > 0
            single = {n: cert[:, n - 4].mean() for n in (4, 8, 12, 20, 40, 80, 160)}
            ever = cert.any(1).mean()
            se = lambda q: math.sqrt(q * (1 - q) / R)
            exc = [n for n, q in single.items() if q - 2 * se(q) > eta] + (["ever"] if ever - 2 * se(ever) > eta else [])
            if exc and first is None:
                first = (name, eta, exc)
            if "skew-right" in name and eta == 0.05 or exc:
                print(f"  {name:22s} eta={eta}: n=4 {single[4]:.4f}, n=20 {single[20]:.4f}, n=40 {single[40]:.4f}, ever {ever:.4f}; "
                      f"exceeds (est - 2SE > eta) at: {exc if exc else 'none'}")
    print(f"\nfirst exceedance found: {first}")
    print(f"\nFailures: {len(fails)}")
    for f in fails:
        print(" -", f)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
