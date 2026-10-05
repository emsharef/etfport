"""Red's check of claim 112 (mathb/m8-model), written without reading checks/112. Supports inferred from the claim's numbers
(M8 does not state them): z^f in {+-7.6, +-8.4}%, z^A in {+-4, +-8}%, z^E in {+-0.5}%, each equiprobable; theta two points per block.
Dynamic optimum = the lifted joint concave program over the 72 public nodes (exact, no grid)."""
import itertools, numpy as np, cvxpy as cp
from collections import defaultdict
bA, bE, cE = 0.9, 1.0, 0.0005; lam0, al0, sl, sa = 0.01, 0.004, 0.004, 0.02
ZF = [-0.084, -0.076, 0.076, 0.084]; ZA = [-0.08, -0.04, 0.04, 0.08]; ZE = [-0.005, 0.005]
sf2, sA2, sE2 = np.mean(np.square(ZF)), np.mean(np.square(ZA)), np.mean(np.square(ZE))
GAM, BETA = 2.5, 1.0; KP = np.array([0.005, 0.001]); KM = KP.copy(); CAP = np.array([1.0, 1.0]); X0 = np.array([0.40, 0.0]); H0 = 0.06; BP = 1e4
SOLV = dict(solver=cp.CLARABEL, tol_gap_abs=1e-12, tol_gap_rel=1e-12, tol_feas=1e-12, max_iter=500)


def moments(lh, ah, pl, pa):
    mu = np.array([bA * lh + ah, bE * lh - cE]); s = sf2 + pl
    S = np.array([[bA ** 2 * s + sA2 + pa, bA * bE * s], [bA * bE * s, bE ** 2 * s + sE2]]); return mu, S


pl0, pa0 = sl ** 2, sa ** 2; kl, ka = pl0 / (pl0 + sf2), pa0 / (pa0 + sA2); pl1, pa1 = (1 - kl) * pl0, (1 - ka) * pa0
mu0, S0 = moments(lam0, al0, pl0, pa0)
print(f"sf {np.sqrt(sf2):.4%} sA {np.sqrt(sA2):.4%} sE {np.sqrt(sE2):.3%}; P0 ({pl0:.3e}, {pa0:.3e}); gains k_l {kl:.4f} k_a {ka:.4f}; P1 ({pl1:.4e}, {pa1:.4e})")
print(f"info form: {abs(1 / pl1 - 1 / pl0 - 1 / sf2):.1e} {abs(1 / pa1 - 1 / pa0 - 1 / sA2):.1e}")
print(f"mu0 {mu0 * 100}; Sigma0 {S0.round(5).tolist()}; target {np.linalg.solve(GAM * S0, mu0).round(3)}; min eig {np.linalg.eigvalsh(S0).min():.2e}")

# the tree: hidden branches -> public nodes (f, residual_A, z^E)
nodes = defaultdict(lambda: dict(q=0.0, th=np.zeros(2)))
nb = 0
for lam, al, zf, za, ze in itertools.product([lam0 - sl, lam0 + sl], [al0 - sa, al0 + sa], ZF, ZA, ZE):
    p = 1 / 128; nb += 1
    key = (round(lam + zf, 6), round(al + za, 6), ze); n = nodes[key]; n['q'] += p; n['th'] += p * np.array([lam, al])
N = []
for (f, ra, ze), n in nodes.items():
    post = n['th'] / n['q']; filt = np.array([lam0 + kl * (f - lam0), al0 + ka * (ra - al0)])
    rA = bA * f + ra; rE = bE * f - cE + ze
    N.append(dict(f=f, ra=ra, ze=ze, q=n['q'], post=post, filt=filt, g=np.array([1 + rA, 1 + rE])))
q = np.array([n['q'] for n in N]); gap = np.array([n['post'] - n['filt'] for n in N])
print(f"{nb} hidden branches, {len(N)} public nodes, sum q {q.sum():.12f}; min gross return {min(n['g'].min() for n in N):.4f}")
print(f"max |posterior - filter|: premium {np.abs(gap[:, 0]).max():.4%}, alpha {np.abs(gap[:, 1]).max():.4%}; E gap {q @ gap}")
eps = np.array([n['filt'] - [lam0, al0] for n in N])
print(f"innovation: mean {q @ eps}, cov {np.diag((eps * q[:, None]).T @ eps)} vs V0 ({pl0 - pl1:.4e}, {pa0 - pa1:.4e}); cross {(q * eps[:, 0]) @ eps[:, 1]:.1e}")
mu1 = {id(n): moments(*n['filt'], pl1, pa1) for n in N}
for nm, key in (("A", (0.09, 0.064)), ("B", (0.098, 0.104))):
    for n in N:
        if abs(n['f'] - key[0]) < 1e-9 and abs(n['ra'] - key[1]) < 1e-9:
            print(f"node {nm} (z^E {n['ze']:+.3f}): q {n['q']:.4f} (both z^E: {2 * n['q']:.4f}); filter {n['filt'] * 100}, posterior {n['post'] * 100}")


def one_review(mu, S, xm, h):
    x = cp.Variable(2); up = cp.Variable(2, nonneg=True); dn = cp.Variable(2, nonneg=True); c = KP @ up + KM @ dn
    b = h - cp.sum(x - xm) - c >= 0; L = np.linalg.cholesky(S)
    pr = cp.Problem(cp.Maximize(BP * (mu @ x - GAM / 2 * cp.sum_squares(L.T @ x) - c)), [x - xm == up - dn, x >= 0, x <= CAP, b]); pr.solve(**SOLV)
    return x.value, float(b.dual_value) / BP, pr.value / BP


def score(mu, S, x, xm): return mu @ x - GAM / 2 * x @ S @ x - KP @ np.maximum(x - xm, 0) - KM @ np.maximum(xm - x, 0)


xm0, eta0, _ = one_review(mu0, S0, X0, H0); gm = mu0 - GAM * S0 @ xm0
hm = H0 - np.sum(xm0 - X0) - KP @ np.maximum(xm0 - X0, 0) - KM @ np.maximum(X0 - xm0, 0)
print(f"myopic review 0: x {xm0.round(5)}, cash {hm:.2e}, eta {eta0:.4%}; marginals g {gm * 100}; fund buy line eta+(1+eta)k+ = {eta0 + (1 + eta0) * KP[0]:.4%}, ETF buy line {eta0 + (1 + eta0) * KP[1]:.4%}")
vm = score(mu0, S0, xm0, X0); X1m = []
for n in N:
    m, S = mu1[id(n)]; x1, e1, v1 = one_review(m, S, n['g'] * xm0, hm); vm += BETA * n['q'] * v1; X1m.append((x1, e1))
print(f"myopic value {vm:.7f}")

# dynamic: the lifted joint concave program
x0 = cp.Variable(2); u0p = cp.Variable(2, nonneg=True); u0m = cp.Variable(2, nonneg=True); c0 = KP @ u0p + KM @ u0m; h0 = H0 - cp.sum(x0 - X0) - c0
cons = [x0 - X0 == u0p - u0m, x0 >= 0, x0 <= CAP, h0 >= 0]; obj = mu0 @ x0 - GAM / 2 * cp.sum_squares(np.linalg.cholesky(S0).T @ x0) - c0
for n in N:
    m, S = mu1[id(n)]; x1 = cp.Variable(2); up = cp.Variable(2, nonneg=True); dn = cp.Variable(2, nonneg=True); c1 = KP @ up + KM @ dn
    cons += [x1 - cp.multiply(n['g'], x0) == up - dn, x1 >= 0, x1 <= CAP, h0 - cp.sum(x1 - cp.multiply(n['g'], x0)) - c1 >= 0]
    obj = obj + BETA * n['q'] * (m @ x1 - GAM / 2 * cp.sum_squares(np.linalg.cholesky(S).T @ x1) - c1)
pr = cp.Problem(cp.Maximize(BP * obj), cons); pr.solve(**SOLV)
print(f"dynamic review 0: x {x0.value.round(5)}, value {pr.value / BP:.7f}; dynamic - myopic {pr.value / BP - vm:.2e}; |x0 - xm0| {np.abs(x0.value - xm0).max():.1e}")
for nm, key in (("A", (0.09, 0.064)), ("B", (0.098, 0.104))):
    for n, (x1, e1) in zip(N, X1m):
        if abs(n['f'] - key[0]) < 1e-9 and abs(n['ra'] - key[1]) < 1e-9:
            m, S = mu1[id(n)]
            print(f"node {nm} z^E {n['ze']:+.3f}: marked {(n['g'] * xm0).round(4)}, mu1 {m * 100}, target {np.linalg.solve(GAM * S, m).round(3)}; myopic review 1 x {x1.round(4)}, eta {e1:.4%}")
# node A: the cash-price interval (no trade, zero cash): every eta with both instruments' held lines satisfied
for n, (x1, e1) in zip(N, X1m):
    if abs(n['f'] - 0.09) < 1e-9 and abs(n['ra'] - 0.064) < 1e-9:
        m, S = mu1[id(n)]; g = m - GAM * S @ x1
        lo = max((g[i] - KP[i]) / (1 + KP[i]) for i in range(2)); hi = min((g[i] + KM[i]) / (1 - KM[i]) for i in range(2))
        print(f"node A z^E {n['ze']:+.3f}: marginals {g * 100}; admissible eta in [{max(lo, 0):.4%}, {hi:.4%}]")
# the claim's fund-marginal display vs claim 110's decomposition at review 0
rho = S0[0, 1] / S0[1, 1]; v = S0[0, 0] - S0[0, 1] ** 2 / S0[1, 1]; at = mu0[0] - rho * mu0[1]
print(f"rho {rho:.4f}, v {v:.5f}, alpha~ {at:.4%}: alpha~ + rho g_E - gam v a = {at + rho * gm[1] - GAM * v * xm0[0]:.4%}; claim's 0.4% + 0.9 m - gam (sA2+pa0) a = {0.004 + 0.9 * 0.00275 - GAM * (sA2 + pa0) * 0.4:.4%}")
