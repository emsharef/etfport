"""Red's reproduction of claim 112's Table 5 stage scores and Table 6 (experiment 050), reusing red_reproduce.py's tree."""
import io, contextlib, itertools, numpy as np, cvxpy as cp
with contextlib.redirect_stdout(io.StringIO()): import red_reproduce as T
# posterior second moments per node
M2 = {}
for lam, al, zf, za, ze in itertools.product([T.lam0 - T.sl, T.lam0 + T.sl], [T.al0 - T.sa, T.al0 + T.sa], T.ZF, T.ZA, T.ZE):
    key = (round(lam + zf, 6), round(al + za, 6), ze); M2.setdefault(key, np.zeros(2)); M2[key] += np.array([lam ** 2, al ** 2]) / 128
for n in T.N:
    key = (round(n['f'], 6), round(n['ra'], 6), n['ze']); var = M2[key] / n['q'] - n['post'] ** 2; n['pvar'] = np.maximum(var, 0)
    n['B'] = T.moments(n['post'][0], n['post'][1], n['pvar'][0], n['pvar'][1]); n['F'] = T.mu1[id(n)]
q = np.array([n['q'] for n in T.N])
print(f"posterior variances: revealing-block zeros {sum((n['pvar'] < 1e-14).sum() for n in T.N)}, max {max(n['pvar'].max() for n in T.N):.3e} vs prior ({T.pl0:.1e}, {T.pa0:.1e})")


def myopic(key):
    xm0, _, _ = T.one_review(T.mu0, T.S0, T.X0, T.H0); h0 = T.H0 - T.spend(xm0, T.X0) if hasattr(T, 'spend') else None
    h0 = T.H0 - np.sum(xm0 - T.X0) - T.KP @ np.maximum(xm0 - T.X0, 0) - T.KM @ np.maximum(T.X0 - xm0, 0); h0 = max(h0, 0.0)
    return xm0, [T.one_review(*n[key], n['g'] * xm0, h0)[0] for n in T.N]


def dynamic(key):
    x0 = cp.Variable(2); u0 = cp.Variable(2, nonneg=True); d0 = cp.Variable(2, nonneg=True); c0 = T.KP @ u0 + T.KM @ d0; h0 = T.H0 - cp.sum(x0 - T.X0) - c0
    cons = [x0 - T.X0 == u0 - d0, x0 >= 0, x0 <= T.CAP, h0 >= 0]; obj = T.mu0 @ x0 - T.GAM / 2 * cp.sum_squares(np.linalg.cholesky(T.S0).T @ x0) - c0; X = []
    for n in T.N:
        m, S = n[key]; x1 = cp.Variable(2); u = cp.Variable(2, nonneg=True); d = cp.Variable(2, nonneg=True); c1 = T.KP @ u + T.KM @ d
        cons += [x1 - cp.multiply(n['g'], x0) == u - d, x1 >= 0, x1 <= T.CAP, h0 - cp.sum(x1 - cp.multiply(n['g'], x0)) - c1 >= 0]; X.append(x1)
        obj = obj + n['q'] * (m @ x1 - T.GAM / 2 * cp.sum_squares(np.linalg.cholesky(S + 1e-14 * np.eye(2)).T @ x1) - c1)
    cp.Problem(cp.Maximize(T.BP * obj), cons).solve(**T.SOLV); return x0.value, [x.value for x in X]


def yard(x0, X1):  # review-0 prior predictive moments; review 1 the posterior (true conditional) moments
    return T.score(T.mu0, T.S0, x0, T.X0) + sum(n['q'] * T.score(*n['B'], x1, n['g'] * x0) for n, x1 in zip(T.N, X1))


for name, pol in (("myopic", myopic), ("dynamic", dynamic)):
    xF, XF = pol('F'); xB, XB = pol('B'); vF, vB = yard(xF, XF), yard(xB, XB)
    diff = [np.abs(a - b).max() > 1e-6 for a, b in zip(XF, XB)]
    print(f"{name}: root filter {xF.round(4)} exact {xB.round(4)}; values filter {vF:.6f} exact {vB:.6f}, gain {(vB - vF) * 1e4:.2f} bp; review-1 decisions differ at {sum(diff)} of 72 public nodes (prob {q[diff].sum():.3f})")
    for nm, key in (("A", (0.09, 0.064)), ("B", (0.098, 0.104))):
        for n, a, b in zip(T.N, XF, XB):
            if abs(n['f'] - key[0]) < 1e-9 and abs(n['ra'] - key[1]) < 1e-9 and n['ze'] > 0: print(f"   node {nm}: filter {a.round(4)} exact {b.round(4)}")
# Table 5's stage scores at nodes A and B, under both conventions
xm0, XF = myopic('F')
for nm, key in (("A", (0.09, 0.064)), ("B", (0.098, 0.104))):
    for n, x1 in zip(T.N, XF):
        if abs(n['f'] - key[0]) < 1e-9 and abs(n['ra'] - key[1]) < 1e-9 and n['ze'] > 0:
            print(f"Table 5 node {nm}: posterior mean with the filter's Sigma_1 {T.score(n['B'][0], n['F'][1], x1, n['g'] * xm0):.6f}; posterior mean and covariance {T.score(*n['B'], x1, n['g'] * xm0):.6f}")
