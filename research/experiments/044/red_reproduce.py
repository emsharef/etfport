"""Red's reproduction of experiment 044 (claim 109), written without reading run.py or report.py. Red's own solver and
criterion code (its claim 109 review's red109.py; argument 1 is its directory) on this Design's instance rules, with red's
own seeds: 040's draws, ETF rates U[0, 50 bp], fees U[0, 20 bp], ETF incumbents 0 w.p. 1/2 else U[0, 0.5], and the cash
h^- = max(need x U(0.3, 1.5), 1e-3) from a first solve without the budget."""
import sys; sys.path.insert(0, sys.argv[1])
import numpy as np, cvxpy as cp, warnings
from multiprocessing import Pool
import red109 as R
warnings.simplefilter('ignore'); GAM, BP, SOLV = R.GAM, R.BP, R.SOLV
_solve = R.solve
def safe_solve(*args, **kw):
    try: return _solve(*args, **kw)
    except Exception: return None
R.solve = safe_solve
SF = np.diag([0.08 ** 2, 0.04 ** 2])


def draw(seed):
    rng = np.random.default_rng([4044, seed]); one = seed % 2 == 1
    if one: BA = np.array([[1, 0.5]]) if rng.random() < 0.5 else np.array([[1, -0.3]]); xb = rng.choice([0.25, 2.0])
    else: BA = np.array([[1, 0.5], [1, 0.2], [1, -0.3]]); xb = rng.choice([0.25, 1.0])
    N = BA.shape[0]; sd = rng.uniform(0.001, 0.01, 2)
    I = dict(BE=np.eye(2), BA=BA, Sf=SF + np.diag(sd ** 2), lam=rng.uniform(-0.01, 0.03, 2), cE=rng.uniform(0, 0.002, 2), ah=rng.uniform(-0.01, 0.01, N),
             V=0.02 ** 2 * (1 + rng.uniform(0.01, 3, N)), kpA=rng.uniform(0, 0.02, N), kmA=rng.uniform(0, 0.02, N), kpE=rng.uniform(0, 0.005, 2), kmE=rng.uniform(0, 0.005, 2),
             SE=np.zeros((2, 2)), xb=np.full(N, xb), x0E=np.where(rng.random(2) < 0.5, 0.0, rng.uniform(0, 0.5, 2)), h=10.0)
    I['x0A'] = rng.uniform(0, 1, N) * xb
    r0 = R.solve(I)
    if r0 is None: return None
    x = r0[0]; mu, Sig, kp, km, x0 = R.mom(I)
    need = np.sum(x - x0) + kp @ np.maximum(x - x0, 0) + km @ np.maximum(x0 - x, 0)
    I['h'] = max(need * rng.uniform(0.3, 1.5), 1e-3)
    return I


def one(seed):
    I = draw(seed)
    if I is None: return None
    N = len(I['ah']); M = 2
    J = R.solve(I)
    if J is None: return None
    x, eta, Jv, kJ = J; mu, Sig, kp, km, x0 = R.mom(I); g = mu - GAM * Sig @ x; xA, xE = x[:N], x[N:]
    Q = I['BA'].T.copy(); SEE = I['Sf']; muE = I['lam'] - I['cE']; at = I['ah'] + Q.T @ I['cE']; tol = 1e-7
    Z = [j for j in range(M) if xE[j] <= tol]; Bs = [j for j in range(M) if xE[j] > I['x0E'][j] + tol]
    Ss = [j for j in range(M) if tol < xE[j] < I['x0E'][j] - tol]; Is = [j for j in range(M) if j not in Z + Bs + Ss]; T = Bs + Ss; F = Z + Is
    t = np.array([I['kpE'][j] if j in Bs else -I['kmE'][j] for j in T]); piT = eta + (1 + eta) * t; w = xE + Q @ xA
    out = dict(bind=eta > 1e-7)
    if T:
        wT = np.linalg.solve(SEE[np.ix_(T, T)], (muE[T] - piT) / GAM - (SEE[np.ix_(T, F)] @ w[F] if F else 0)); out['wT'] = float(np.abs(wT - w[T]).max())
    if F:
        K = SEE[np.ix_(F, T)] @ np.linalg.inv(SEE[np.ix_(T, T)]) if T else np.zeros((len(F), 0))
        muFT = muE[F] - (K @ muE[T] if T else 0); SFFT = SEE[np.ix_(F, F)] - (K @ SEE[np.ix_(T, F)] if T else 0)
        gF = muFT + (K @ piT if T else 0) - GAM * SFFT @ w[F]; out['gF'] = float(np.abs(gF - g[N:][F]).max())
    Gerr = 0.0
    for i in range(N):
        rT, rF = Q[T, i], Q[F, i]
        rho = rT + (np.linalg.solve(SEE[np.ix_(T, T)], SEE[np.ix_(T, F)] @ rF) if (T and F) else 0 * rT)
        aFT = at[i] + ((rF @ muFT - GAM * rF @ SFFT @ xE[F]) if F else 0) + (rho @ piT if T else 0)
        VFT = I['V'][i] * np.eye(N)[i] + ((Q[F, :].T @ SFFT @ Q[F, :])[i] if F else 0)
        Gerr = max(Gerr, abs(aFT - GAM * VFT @ xA - g[i]))
    out['G'] = Gerr
    # 2d over ETFs starting at zero: the one-quantity test
    thr = lambda j: eta + (1 + eta) * I['kpE'][j]
    out['z0'] = [((g[N + j] + GAM * SEE[j, j] * xE[j] <= thr(j) + 1e-9) == (xE[j] <= tol)) for j in range(M) if I['x0E'][j] <= 0]
    # part 4: claim 041's stage 1 over W_F, the fibre with every friction and the budget
    xa = cp.Variable(N); wv = cp.Variable(M); L = np.linalg.cholesky(SEE)
    cp.Problem(cp.Maximize(BP * (muE @ wv - GAM / 2 * cp.sum_squares(L.T @ wv))), [wv >= Q @ xa, xa >= 0, xa <= I['xb']]).solve(**SOLV)
    ws = wv.value; zs = GAM * SEE @ ws - muE
    f2 = R.solve(I, fibre_w=ws)
    if f2 is not None:
        x2, eta2, T2, k2 = f2; exact = np.abs(x2 - x).max() <= 1e-5
        lo, hi = 0.0, (np.inf if k2 <= 1e-9 else 0.0)
        def add(G, kpl, kmi, xv, x0v, cap):
            nonlocal lo, hi
            up, dn = xv > x0v + 1e-7, xv < x0v - 1e-7
            if up and xv < cap - 1e-7: e = (G - kpl) / (1 + kpl); lo, hi = max(lo, e - 1e-8), min(hi, e + 1e-8)
            elif up: hi = min(hi, (G - kpl) / (1 + kpl) + 1e-8)
            elif dn and xv > 1e-7: e = (G + kmi) / (1 - kmi); lo, hi = max(lo, e - 1e-8), min(hi, e + 1e-8)
            elif dn: lo = max(lo, (G + kmi) / (1 - kmi) - 1e-8)
            else:
                if xv < cap - 1e-7: lo = max(lo, (G - kpl) / (1 + kpl) - 1e-8)
                if xv > 1e-7: hi = min(hi, (G + kmi) / (1 - kmi) + 1e-8)
        for i in range(N): add(at[i] - GAM * I['V'][i] * x2[i] - Q[:, i] @ zs, I['kpA'][i], I['kmA'][i], x2[i], I['x0A'][i], I['xb'][i])
        for j in range(M): add(-zs[j], I['kpE'][j], I['kmE'][j], x2[N + j], I['x0E'][j], np.inf)
        kinds = []
        for j in range(M):
            e2, e0 = x2[N + j], I['x0E'][j]
            kinds.append('zero' if e2 <= 1e-7 and e0 <= 1e-7 else ('sold to zero' if e2 <= 1e-7 else ('bought interior' if e2 > e0 + 1e-7 else ('sold interior' if e2 < e0 - 1e-7 else 'untraded interior'))))
        out.update(fund=True, exact=bool(exact), crit=bool(lo <= hi), kinds=tuple(kinds), interior_trade=any(k in ('bought interior', 'sold interior') for k in kinds))
    else:
        out['fund'] = False
    wTB = np.linalg.solve(GAM * SEE, muE)
    rs = R.solve(I, extra_lin=np.zeros(N + M))       # unconstrained stage 1: nu = 0, the tilt vanishes
    out['soft'] = float(np.abs(rs[0] - x).max())
    rs2 = R.solve(I, extra_lin=np.concatenate([Q.T @ zs, zs]))
    if rs2 is None or rs is None: return out | dict(bound=True, soft=0.0, failed_soft=True)
    xs = rs2[0]; val = mu @ xs - GAM / 2 * xs @ Sig @ xs - kp @ np.maximum(xs - x0, 0) - km @ np.maximum(x0 - xs, 0)
    Ls = Jv - val; out['bound'] = bool(-1e-9 <= Ls <= zs @ ((xs[N:] + Q @ xs[:N]) - w) + 1e-9)
    return out


if __name__ == "__main__":
    with Pool(9) as p: RAW = p.map(one, range(1000))
    O = [o for o in RAW if o]; print(f'solver failures set aside: {sum(o is None for o in RAW)}')
    print(f"{len(O)} draws, budget binding at {sum(o['bind'] for o in O)}")
    print(f"part 2: 2a max {max(o.get('wT', 0) for o in O):.1e} ({sum('wT' in o for o in O)} draws); 2b max {max(o.get('gF', 0) for o in O):.1e} ({sum('gF' in o for o in O)}); 2c max {max(o['G'] for o in O):.1e}")
    z0 = [v for o in O for v in o['z0']]; print(f"2d one-quantity test: {sum(z0)}/{len(z0)} ETFs starting at zero")
    F = [o for o in O if o['fund']]; import collections
    print(f"part 4a: fundable {len(F)} (unfundable {len(O) - len(F)}); criterion = exactness at {sum(o['crit'] == o['exact'] for o in F)}/{len(F)}; exact {sum(o['exact'] for o in F)}")
    print(f"4b: exact kinds {dict(collections.Counter(o['kinds'] for o in F if o['exact']))}; exact with an interior ETF trade: {sum(o['exact'] and o['interior_trade'] for o in F)}; exact with binding budget: {sum(o['exact'] and o['bind'] for o in F)}")
    print(f"4c: unconstrained soft max |x_s - x_J| {max(o['soft'] for o in O):.1e}; W_F soft bound holds {sum(o['bound'] for o in O)}/{len(O)}")
