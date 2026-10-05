"""Red's bounded reproduction of experiment 043 part 4 (claim 042), written without reading run.py or report.py: the fund's
band at the ETF incumbent p^- = p* (Deviation 4's measure) at the coarsest registered step eps = 0.2, corr 0.9, xi in {1/4, 4},
against one-instrument DPs at the same step (the free and frozen ends). Average-cost relative value iteration on a lazy walk
(stay 1/2; otherwise the four-point target law with r = 0), with the value extended beyond the grid by slope kappa per axis
(Deviation 2's rule). Parts 1-3 and Deviations 2 and 4 are covered in red's Review from red's earlier independent tests."""
import sys; sys.path.insert(0, sys.argv[1])
import numpy as np
from red_reproduce import l1min
GAM = 5.0; SEE = 0.0854 ** 2; SAA = 0.0854 ** 2 + 0.02 ** 2


def shift_ext(V, i, j, kA, kE, hA, hE):
    """V(d - eps) for a shift of (i, j) grid steps, extended linearly beyond the grid with slopes kappa."""
    nA, nE = V.shape; out = np.empty_like(V)
    ia = np.arange(nA) - i; je = np.arange(nE) - j
    ca, ce = np.clip(ia, 0, nA - 1), np.clip(je, 0, nE - 1)
    out = V[np.ix_(ca, ce)] + kA * hA * np.abs(ia - ca)[:, None] + kE * hE * np.abs(je - ce)[None, :]
    return out


def rvi2(c, kA, kE, u, h, law, S, nA, nE, iters):
    a = (np.arange(nA) - nA // 2) * h; e = (np.arange(nE) - nE // 2) * h
    D1, D2 = np.meshgrid(a, e, indexing='ij'); Q = GAM / 2 * (S[0, 0] * D1 ** 2 + 2 * S[0, 1] * D1 * D2 + S[1, 1] * D2 ** 2)
    V = np.zeros((nA, nE))
    for _ in range(iters):
        W = Q + 0.5 * V + sum(p * shift_ext(V, i, j, kA, kE, h, h) for (i, j), p in law)
        U = l1min(W, kE, kE, h, 1); Vn = l1min(U, kA, kA, h, 0); V = Vn - Vn[nA // 2, nE // 2]
    held = (U - Vn) <= 1e-12 * np.abs(W).max()
    col = held[:, nE // 2]; idx = np.where(col)[0]
    return (a[idx[-1]] - a[idx[0]]) / 2


def rvi1(c, k, h, jumps, n, iters):
    y = (np.arange(n) - n // 2) * h; V = np.zeros(n)
    for _ in range(iters):
        W = c / 2 * y ** 2 + 0.5 * V
        for s, p in jumps:
            ii = np.arange(n) - s; cc = np.clip(ii, 0, n - 1); W = W + p * (V[cc] + k * h * np.abs(ii - cc))
        Vn = l1min(W[:, None], k, k, h, 0)[:, 0]; V = Vn - Vn[n // 2]
    idx = np.where(W - Vn <= 1e-12 * np.abs(W).max())[0]
    return (y[idx[-1]] - y[idx[0]]) / 2


def main():
    corr = 0.9; SAE = corr * np.sqrt(SAA * SEE); S = np.array([[SAA, SAE], [SAE, SEE]])
    rho_h, rho_p = SAE / SEE, SAE / SAA; cres = GAM * (SAA - SAE ** 2 / SEE); kA = 0.001
    eps = 0.2
    for xi in (0.25, 4.0):
        # lazy law: v_A = v_B = u^2/2 per review; Delta_free^3 = 3 (2 kA) v_A / (4 cres); eps = sqrt(v_A)/Delta_free
        # => u from eps: Delta_free = (3 * 2kA * v/(4 cres))^(1/3), v = (eps Delta)^2 -> Delta = 3*2kA*eps^2/(4 cres)
        D_free = 3 * 2 * kA * eps ** 2 / (4 * cres); v = (eps * D_free) ** 2; u = np.sqrt(2 * v)
        vBeff = v + rho_h ** 2 * v
        kE = xi ** 3 * kA * (v / vBeff) * (GAM * SEE / cres)          # xi^3 = (kE/kA)(vBeff/vA)(cres/(gamma SEE))
        D_E = (3 * 2 * kE * vBeff / (4 * GAM * SEE)) ** (1 / 3)
        vid = v + rho_p ** 2 * v; D_froz = (3 * 2 * kA * vid / (4 * GAM * SAA)) ** (1 / 3)
        h = u / 4; st = 4
        nA = int(2 * (3 * max(D_free, D_froz) + 10 * u) / h) + 1; nE = int(2 * (1.5 * (D_E + abs(rho_h) * 3 * max(D_free, D_froz)) + 10 * u) / h) + 1
        law = [((st, st), 1 / 8), ((-st, -st), 1 / 8), ((st, -st), 1 / 8), ((-st, st), 1 / 8)]
        its = int(8 * ((max(D_E, D_free, D_froz) / u) ** 2) * 4) + 500
        F = rvi2(cres, kA, kE, u, h, law, S, nA, nE, its) / D_free
        # ends at the same step and lazy law: free (cres, fund +-u); frozen (gamma SAA, idle target Delta a* + rho' Delta b*, rounded to h/40)
        hf = h / 10; n1 = int(2 * (4 * max(D_free, D_froz) + 10 * u) / hf) + 1
        free = rvi1(cres, kA, hf, [(40, 0.25), (-40, 0.25)], n1, its) / D_free
        jp = int(round((1 + rho_p) * u / hf)); jm = int(round((1 - rho_p) * u / hf))
        froz = rvi1(GAM * SAA, kA, hf, [(jp, 1 / 8), (-jp, 1 / 8), (jm, 1 / 8), (-jm, 1 / 8)], n1, its) / D_free
        print(f"corr {corr}, xi {xi}, eps {eps}: F = {F:.3f}; free end {free:.3f}; frozen end (DP) {froz:.3f}, formula {D_froz / D_free:.3f}; "
              f"F - free {(F - free) * D_free / h:+.1f} and F - frozen {(F - froz) * D_free / h:+.1f} grid steps; {its} reviews; grid {nA}x{nE}", flush=True)


if __name__ == "__main__":
    main()
