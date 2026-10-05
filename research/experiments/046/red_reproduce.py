"""Red's bounded reproduction of experiment 046 (claim 043), written without reading run.py or report.py.
Two-instrument average-cost relative value iteration (lazy four-point walk, r = 0, grid step u/4, value extended beyond the
grid with slope kappa per axis), gain = the pair's cost per review; one-instrument lattice gains at the same step for the
term-wise ratios r_A, r_E of Deviation 2. Cells: part 2 (corr 0), part 1 at xi = 4 (resolved) and part 4(c) (xi 1, 4, 8),
all at eps = 0.2. Argument 1: a directory holding red's 036 red_reproduce.py (for the L1 transform)."""
import sys; sys.path.insert(0, sys.argv[1])
import numpy as np
from red_reproduce import l1min
GAM = 5.0; SEE = 0.0854 ** 2; SAA = 0.0854 ** 2 + 0.02 ** 2; kA = 0.001


def aone(c, v, k): return (c / 2) * (3 * 2 * k * v / (4 * c)) ** (2 / 3) if k > 0 else 0.0


def ext_shift(V, i, j, ka, ke, h):
    nA, nE = V.shape; ia = np.arange(nA) - i; je = np.arange(nE) - j; ca, ce = np.clip(ia, 0, nA - 1), np.clip(je, 0, nE - 1)
    return V[np.ix_(ca, ce)] + ka * h * np.abs(ia - ca)[:, None] + ke * h * np.abs(je - ce)[None, :]


def gain2(S, ke, u, h, nA, nE, iters):
    st = int(round(u / h)); a = (np.arange(nA) - nA // 2) * h; e = (np.arange(nE) - nE // 2) * h
    D1, D2 = np.meshgrid(a, e, indexing='ij'); Q = GAM / 2 * (S[0, 0] * D1 ** 2 + 2 * S[0, 1] * D1 * D2 + S[1, 1] * D2 ** 2)
    law = [((st, st), 1 / 8), ((-st, -st), 1 / 8), ((st, -st), 1 / 8), ((-st, st), 1 / 8)]; V = np.zeros((nA, nE)); gs = []
    for _ in range(iters):
        W = Q + 0.5 * V + sum(p * ext_shift(V, i, j, kA, ke, h) for (i, j), p in law)
        Vn = l1min(l1min(W, ke, ke, h, 1), kA, kA, h, 0); g = Vn[nA // 2, nE // 2]; V = Vn - g; gs.append(g)
    return gs[-1], abs(gs[-1] - gs[-min(1000, len(gs) // 2)]) / gs[-1]


def gain1(c, k, u, h, n, iters):
    """one instrument, lazy walk +-u with prob 1/4 each (the marginal of the four-point lazy law), slope extension."""
    st = int(round(u / h)); y = (np.arange(n) - n // 2) * h; V = np.zeros(n)
    for _ in range(iters):
        W = c / 2 * y ** 2 + 0.5 * V
        for s, p in ((st, 0.25), (-st, 0.25)):
            ii = np.arange(n) - s; cc = np.clip(ii, 0, n - 1); W = W + p * (V[cc] + k * h * np.abs(ii - cc))
        Vn = l1min(W[:, None], k, k, h, 0)[:, 0]; g = Vn[n // 2]; V = Vn - g
    return g


def cell(corr, xi, eps=0.2):
    SAE = corr * np.sqrt(SAA * SEE); S = np.array([[SAA, SAE], [SAE, SEE]]); rho = SAE / SEE
    cres = GAM * (SAA - SAE ** 2 / SEE); cE = GAM * SEE
    D_free = 3 * 2 * kA * eps ** 2 / (4 * cres); v = (eps * D_free) ** 2; u = np.sqrt(2 * v); h = u / 4
    vBeff = v + rho ** 2 * v
    kE = xi ** 3 * kA * (v / vBeff) * (cE / cres)
    D_E = (3 * 2 * kE * vBeff / (4 * cE)) ** (1 / 3); D_up = (3 * 2 * (kA + abs(rho) * kE) * v / (4 * cres)) ** (1 / 3)
    D_froz = (3 * 2 * kA * (v + (SAE / SAA) ** 2 * v) / (4 * GAM * SAA)) ** (1 / 3); Dm = max(D_free, D_froz)   # grid as in experiment 043
    nA = int(2 * (3 * Dm + 10 * u) / h) + 1; nE = int(2 * (1.5 * (D_E + abs(rho) * 3 * Dm) + 10 * u) / h) + 1
    its = min(int(10 * max(D_E, Dm) ** 2 / v) + 800, 4000)                                                      # bounded (the human's instruction)
    a, drift = gain2(S, kE, u, h, nA, nE, its)
    # term-wise lattice ratios (Deviation 2): one-instrument lattice gain over its formula at the same step
    rA = gain1(cres, kA, u, h, nA, its) / aone(cres, v, kA)
    uE = np.sqrt(2 * vBeff); nE1 = int(2 * (3 * D_E + 10 * uE) / h) + 1
    rE = gain1(cE, kE, uE, uE / max(4, round(uE / h)), max(nE1, 50), its) / aone(cE, vBeff, kE)
    up = rA * aone(cres, v, kA + abs(rho) * kE) + rE * aone(cE, vBeff, kE)
    ks = np.linspace(0, min(kE, kA / abs(rho)) if rho != 0 else kE, 401)
    gl = max(rA * aone(cres, v, kA - abs(rho) * k) + rE * aone(cE, vBeff, k) for k in ks) if rho != 0 else rA * aone(cres, v, kA) + rE * aone(cE, vBeff, kE)
    cb = cres * cE / (cres + rho ** 2 * cE); ab = rE * aone(cb, v, kE)
    dec = rA * aone(cres, v, kA) + rE * aone(cE, vBeff, kE)
    return dict(corr=corr, xi=xi, a=a, up=up, gl=gl, ab=ab, dec=dec, rA=rA, rE=rE, drift=drift, its=its)


if __name__ == "__main__":
    for corr, xi in [(0.0, 0.25), (0.0, 4.0), (0.9, 1.0), (0.5, 4.0), (0.9, 4.0)]:
        c = cell(corr, xi)
        print(f"corr {corr}, xi {xi}: a {c['a']:.3e}; r_A {c['rA']:.3f} r_E {c['rE']:.3f}; a/upper {c['a'] / c['up']:.3f}, a/general lower {c['a'] / c['gl']:.3f}, a/a_b {c['a'] / c['ab']:.3f}"
              + (f", a/(r_A a_A + r_E a_E) - 1 = {c['a'] / c['dec'] - 1:+.1e}" if corr == 0 else "") + f"; drift {c['drift']:.1e} over the last reviews ({c['its']} reviews)", flush=True)
