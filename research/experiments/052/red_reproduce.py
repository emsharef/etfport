"""Red's reproduction of experiment 052 (claim 047's formulas), written from the registered Design without reading
experiments/052/run.py. Red's own solver (red's experiment 047 red_reproduce.py, directory argument 1; experiment 048's cells
from red's experiment 048 script, directory argument 2), instances rebuilt from experiment 047's seeds as in red's 049
reproduction. Checked: part 2(b) at the dynamic root and the slack-tomorrow certificate; the bound on N(x^my_0); part 3(b)'s
exact shift and its bound; part 5; part 2(a)'s idle-ETF cases. Part 4's finite-difference slopes and part 2's S_i bound are not
re-run. Run: uv run python experiments/052/red_reproduce.py experiments/047 experiments/048"""
import sys, itertools, numpy as np, cvxpy as cp, warnings, importlib.util
sys.path.insert(0, sys.argv[1])
from multiprocessing import Pool
import red_reproduce as R
warnings.simplefilter('ignore'); TOLV = 1e-7


def load048():
    sp = importlib.util.spec_from_file_location('red048', sys.argv[2] + '/red_reproduce.py'); m = importlib.util.module_from_spec(sp); sp.loader.exec_module(m); return m


def analyst_instance(i, costless=False):
    rng = np.random.default_rng([2047, 1 if costless else 0, i])
    bA = rng.uniform(0.5, 1.5); lam, al = rng.uniform(-0.01, 0.03), rng.uniform(-0.01, 0.01); sl, sa = rng.uniform(0.001, 0.01), rng.uniform(0.0005, 0.004)
    sA = 0.02 * np.sqrt(1 + rng.uniform(0.01, 3)); kAp, kAm = rng.uniform(0, 0.02, 2); kEp, kEm = rng.uniform(0, 0.005, 2); cE = rng.uniform(0, 0.002)
    if costless: kEp = kEm = 0.0
    capA = rng.choice([0.25, 1.0]); x0 = np.array([rng.uniform(0, 1) * capA, 0.0 if rng.random() < 0.5 else rng.uniform(0, 0.5)])
    I = dict(bA=bA, sf=0.08, sA=sA, kp=np.array([kAp, kEp]), km=np.array([kAm, kEm]), cE=cE, cap=capA, x0=x0)
    pl0, pa0 = sl ** 2, sa ** 2; kl, ka = pl0 / (pl0 + 0.08 ** 2), pa0 / (pa0 + sA ** 2); I['m0'] = R.moments(lam, al, pl0, pa0, I); I['Z'] = []
    for (dl, da), (zf, za) in itertools.product(itertools.product([-1, 1], [-1, 1]), itertools.product([-1, 1], [-1, 1])):
        l, a = lam + dl * sl, al + da * sa; f = l + zf * 0.08; res = a + za * sA
        I['Z'].append(dict(q=1 / 16, g=np.array([1 + bA * f + res, 1 + f - cE]), m=R.moments(lam + kl * (f - lam), al + ka * (res - al), (1 - kl) * pl0, (1 - ka) * pa0, I)))
    I['h'] = 10.0; xf, X1 = R.joint(I, budget=False)
    need = R.spend(xf, x0, I) + max([R.spend(x1, z['g'] * xf, I) for z, x1 in zip(I['Z'], X1)] + [0.0]); I['h'] = max(need * rng.uniform(0.2, 1.2), 1e-3)
    return I


def joint_fixA(I, a):
    """the joint program with the root fund holding fixed at a (the reduced point); returns x0, X1."""
    x0 = cp.Variable(2); u0 = cp.Variable(2, nonneg=True); d0 = cp.Variable(2, nonneg=True); c0 = I['kp'] @ u0 + I['km'] @ d0; h0 = I['h'] - cp.sum(x0 - I['x0']) - c0
    mu0, S0 = I['m0']; cons = [x0 - I['x0'] == u0 - d0, x0 >= 0, x0[0] <= I['cap'], h0 >= 0, x0[0] == a]
    obj = mu0 @ x0 - R.GAM / 2 * cp.sum_squares(np.linalg.cholesky(S0).T @ x0) - c0; X1 = []
    for z in I['Z']:
        x1 = cp.Variable(2); u = cp.Variable(2, nonneg=True); d = cp.Variable(2, nonneg=True); c1 = I['kp'] @ u + I['km'] @ d; mu, S = z['m']
        cons += [x1 - cp.multiply(z['g'], x0) == u - d, x1 >= 0, x1[0] <= I['cap'], h0 - cp.sum(x1 - cp.multiply(z['g'], x0)) - c1 >= 0]; X1.append(x1)
        obj = obj + R.BETA * z['q'] * (mu @ x1 - R.GAM / 2 * cp.sum_squares(np.linalg.cholesky(S).T @ x1) - c1)
    cp.Problem(cp.Maximize(R.BP * obj), cons).solve(**R.SOLV); return x0.value, [x.value for x in X1]


def tomorrow_set(I, x0, X1, h0):
    """variables and constraints of tomorrow's lines at (x0, X1): e1(z) >= 0, s1(z, i) = (1 + e1) t_1 (claim 044's sigma)."""
    n = len(I['Z']); e1 = cp.Variable(n, nonneg=True); s1 = cp.Variable((n, 2)); cons = []
    for k, (z, x1) in enumerate(zip(I['Z'], X1)):
        xm = z['g'] * x0; mu, S = z['m']; g1 = mu - R.GAM * S @ x1
        if h0 - R.spend(x1, xm, I) > R.SLACK: cons.append(e1[k] == 0)
        for i in range(2):
            st, atz, atc = R.status(x1, xm, I['cap'], i); ex = g1[i] - e1[k] - s1[k, i]
            if st == 'buy': cons.append(s1[k, i] == (1 + e1[k]) * I['kp'][i])
            elif st == 'sell': cons.append(s1[k, i] == -(1 + e1[k]) * I['km'][i])
            else: cons += [s1[k, i] <= (1 + e1[k]) * I['kp'][i], s1[k, i] >= -(1 + e1[k]) * I['km'][i]]
            if atz and not atc: cons.append(ex <= TOLV)
            elif atc and not atz: cons.append(ex >= -TOLV)
            elif not atz and not atc: cons += [ex <= TOLV, ex >= -TOLV]
    S = [R.BETA * sum(z['q'] * z['g'][i] * (e1[k] + s1[k, i]) for k, z in enumerate(I['Z'])) for i in range(2)]
    Ee = R.BETA * sum(z['q'] * e1[k] for k, z in enumerate(I['Z']))
    return e1, s1, cons, S, Ee


def rng_of(expr, cons):
    lo = cp.Problem(cp.Minimize(expr), cons); lo.solve(solver=cp.CLARABEL); hi = cp.Problem(cp.Maximize(expr), cons); hi.solve(solver=cp.CLARABEL)
    return (lo.value, hi.value) if lo.status == 'optimal' and hi.status == 'optimal' else (np.nan, np.nan)


def etabar_need(I, x0):
    eb, nd = [], []
    for z in I['Z']:
        mu, S = z['m']; eb.append(max(max(mu[i] - I['kp'][i], 0) / (1 + I['kp'][i]) for i in range(2)))
        xh = np.maximum(mu - I['kp'], 0) / (R.GAM * np.diag(S)); nd.append(sum((1 + I['kp'][i]) * max(xh[i] - z['g'][i] * x0[i], 0) for i in range(2)))
    return np.array(eb), np.array(nd)


def lines_lp_extra(I, x0, X1, objective=None, extra=None):
    """part 2's lines as an LP in (eta_0, eta_1(z), sig_0 = (1 + eta_hat) t_0, sig_1(z) = (1 + eta_1) t_1); returns (largest
    violation, eta_0 range) with the complementarity threshold R.SLACK."""
    n = len(I['Z']); e0 = cp.Variable(nonneg=True); e1 = cp.Variable(n, nonneg=True); s0 = cp.Variable(2); s1 = cp.Variable((n, 2)); v = cp.Variable(nonneg=True)
    eh = e0 + R.BETA * sum(z['q'] * e1[k] for k, z in enumerate(I['Z'])); cons = []
    h0 = I['h'] - R.spend(x0, I['x0'], I)
    if h0 > R.SLACK: cons.append(e0 == 0)
    def line(expr, sg, x, xm, kpi, kmi, e, i):
        st, atz, atc = R.status(x, xm, I['cap'], i); c = []
        if st == 'buy': c.append(sg == (1 + e) * kpi)
        elif st == 'sell': c.append(sg == -(1 + e) * kmi)
        else: c += [sg <= (1 + e) * kpi, sg >= -(1 + e) * kmi]
        if atz and atc: pass
        elif atz: c.append(expr <= v)
        elif atc: c.append(expr >= -v)
        else: c += [expr <= v, expr >= -v]
        return c
    Ssum = [0, 0]
    for k, (z, x1) in enumerate(zip(I['Z'], X1)):
        xm = z['g'] * x0; mu, S = z['m']; g1 = mu - R.GAM * S @ x1
        if I['h'] - R.spend(x0, I['x0'], I) - R.spend(x1, xm, I) > R.SLACK: cons.append(e1[k] == 0)
        for i in range(2):
            cons += line(g1[i] - e1[k] - s1[k, i], s1[k, i], x1, xm, I['kp'][i], I['km'][i], e1[k], i)
            Ssum[i] = Ssum[i] + R.BETA * z['q'] * z['g'][i] * (e1[k] + s1[k, i])
    mu0, S0 = I['m0']; g0 = mu0 - R.GAM * S0 @ x0
    for i in range(2): cons += line(g0[i] + Ssum[i] - eh - s0[i], s0[i], x0, I['x0'], I['kp'][i], I['km'][i], eh, i)
    if extra is not None: cons += extra(e0, e1)
    pr = cp.Problem(cp.Minimize(v), cons); pr.solve(solver=cp.CLARABEL); viol = v.value if v.value is not None else np.inf
    rng = None
    if objective == 'range':
        lo = cp.Problem(cp.Minimize(e0), cons + [v <= viol + 1e-9]); lo.solve(solver=cp.CLARABEL); a = e0.value
        hi = cp.Problem(cp.Maximize(e0), cons + [v <= viol + 1e-9, e0 <= 1]); hi.solve(solver=cp.CLARABEL); rng = (a, e0.value)
    return viol, rng


def relaxed(I):
    """the two-review optimum with tomorrow's budget removed (x^s)."""
    x0 = cp.Variable(2); u0 = cp.Variable(2, nonneg=True); d0 = cp.Variable(2, nonneg=True); c0 = I['kp'] @ u0 + I['km'] @ d0; h0 = I['h'] - cp.sum(x0 - I['x0']) - c0
    mu0, S0 = I['m0']; cons = [x0 - I['x0'] == u0 - d0, x0 >= 0, x0[0] <= I['cap'], h0 >= 0]; obj = mu0 @ x0 - R.GAM / 2 * cp.sum_squares(np.linalg.cholesky(S0).T @ x0) - c0
    for z in I['Z']:
        x1 = cp.Variable(2); u = cp.Variable(2, nonneg=True); d = cp.Variable(2, nonneg=True); c1 = I['kp'] @ u + I['km'] @ d; mu, S = z['m']
        cons += [x1 - cp.multiply(z['g'], x0) == u - d, x1 >= 0, x1[0] <= I['cap']]
        obj = obj + R.BETA * z['q'] * (mu @ x1 - R.GAM / 2 * cp.sum_squares(np.linalg.cholesky(S).T @ x1) - c1)
    cp.Problem(cp.Maximize(R.BP * obj), cons).solve(**R.SOLV); return x0.value


def job(arg):
    kind, k = arg
    try:
        I = analyst_instance(k) if kind == 'main' else load048().build(*k)
        mu0, S0 = I['m0']; x0, X1, e0, e1 = R.joint(I); h0 = I['h'] - R.spend(x0, I['x0'], I); _, nd = etabar_need(I, x0); N = nd.max()
        knife = any(1e-7 < abs(x0[i] - I['x0'][i]) < 1e-6 or 1e-7 < x0[i] < 1e-6 for i in range(2)) or lines_lp_extra(I, x0, X1)[0] > 1e-6
        out = dict(kind=kind, k=k, knife=knife)
        zero_ok = lines_lp_extra(I, x0, X1, extra=lambda E0, E1: [E1 == 0])[0] <= 1e-6
        out['p2b'] = (zero_ok if (h0 > R.SLACK and h0 >= N) else None)
        xs = relaxed(I); hs = I['h'] - R.spend(xs, I['x0'], I); _, nds = etabar_need(I, xs)
        out['cert'] = (np.abs(xs - x0).max() <= 1e-5) if (hs > R.SLACK and hs >= nds.max()) else None
        xm0, em0 = R.one_review(mu0, S0, I['x0'], I['h'], I); _, ndm = etabar_need(I, xm0)
        mu1 = np.array([z['m'][0] for z in I['Z']]); S1 = I['Z'][0]['m'][1]; gmin = np.array([z['g'] for z in I['Z']]).min(0)
        rhs = sum((1 + I['kp'][i]) * max(max(mu1[:, i].max() - I['kp'][i], 0) / (R.GAM * S1[i, i]) - gmin[i] * xm0[i], 0) for i in range(2))
        out['Nbound'] = ndm.max() <= rhs + 1e-12
        out['p5'] = (h0 <= N + 1e-9 and (h0 <= 1e-9 or h0 < N)) if not zero_ok else None
        # part 2(a): the ETF idle tomorrow in every state at the dynamic optimum
        idle = all(abs(x1[1] - z['g'][1] * x0[1]) <= 1e-7 for z, x1 in zip(I['Z'], X1))
        out['idle'] = None
        if idle:
            e1v, s1v, cons, S, Ee = tomorrow_set(I, x0, X1, h0); lo, hi = rng_of(S[1], cons)
            out['idle'] = dict(at_zero=x0[1] <= 1e-7, zero_in=lo <= 1e-9 and hi >= -1e-9, moved=abs(x0[1] - xm0[1]) > 1e-5)
        # part 3(b): slack budgets at the one-review root and at the fixed-fund point, ETF interior at both
        out['p3b'] = None
        hm = I['h'] - R.spend(xm0, I['x0'], I)
        if hm > R.SLACK and xm0[1] > 1e-6:
            xf, Xf = joint_fixA(I, xm0[0]); hf = I['h'] - R.spend(xf, I['x0'], I)
            slack1 = all(hf - R.spend(x1, z['g'] * xf, I) > R.SLACK for z, x1 in zip(I['Z'], Xf))
            if hf > R.SLACK and slack1 and xf[1] > 1e-6:
                t1 = []
                for z, x1 in zip(I['Z'], Xf):
                    d = x1[1] - z['g'][1] * xf[1]; t1.append(I['kp'][1] if d > 1e-7 else (-I['km'][1] if d < -1e-7 else (z['m'][0] - R.GAM * z['m'][1] @ x1)[1]))
                SE = R.BETA * sum(z['q'] * z['g'][1] * t for z, t in zip(I['Z'], t1)); cur = R.GAM * S0[1, 1]
                sgn = lambda p: 1 if p > I['x0'][1] + 1e-7 else (-1 if p < I['x0'][1] - 1e-7 else 0)
                same = sgn(xf[1]) == sgn(xm0[1]) != 0
                bound = (R.BETA * max(I['kp'][1], I['km'][1]) * np.mean([z['g'][1] for z in I['Z']]) + I['kp'][1] + I['km'][1]) / cur
                out['p3b'] = dict(same=same, err=abs(xf[1] - xm0[1] - SE / cur) if same else None, within=abs(xf[1] - xm0[1]) <= bound + 1e-12)
        return out
    except cp.error.SolverError:
        return dict(kind=kind, k=k, fail=True)


if __name__ == "__main__":
    E = load048(); cells = list(itertools.product(E.PRE, E.STARTS, [0.005, 1.0], [1, 3], [0.2, 1, 5]))
    with Pool(9) as p: O = p.map(job, [('main', i) for i in range(300)] + [('cell', c) for c in cells])
    F = [o for o in O if o.get('fail')]; K = [o for o in O if not o.get('fail') and not o['knife']]
    print(f"{len(K)} instances after knife edges and solver failures ({len(F)} failures): main {sum(o['kind'] == 'main' for o in K)}, cells {sum(o['kind'] == 'cell' for o in K)}")
    def row(name, key): A = [o[key] for o in K if o[key] is not None]; print(f"  {name}: applies {len(A)}, agrees {sum(bool(a) for a in A)}")
    row("2(b) at the dynamic root: h > 0 and h >= N gives eta_1 = 0 admissible", 'p2b')
    row("2(b) certificate: x^s with h^s > 0 and h^s >= N(x^s) is the dynamic optimum", 'cert')
    row("2(b) N(x^my_0) <= the displayed bound", 'Nbound')
    row("5: priced for every family gives h <= N (strictly when h > 0)", 'p5')
    P = [o['p3b'] for o in K if o['p3b'] is not None]; S = [q for q in P if q['same']]
    print(f"  3(b): hypotheses met {len(P)}; bound holds {sum(q['within'] for q in P)}; same direction today {len(S)}, shift = S_E/(gamma Sigma_EE) within 1e-6 at {sum(q['err'] <= 1e-6 for q in S)} (max error {max((q['err'] for q in S), default=0):.1e})")
    D = [o['idle'] for o in K if o['idle'] is not None]; Z = [d for d in D if d['at_zero']]; Q = [d for d in D if not d['at_zero']]
    print(f"  2(a): ETF idle tomorrow in every state at {len(D)}: at zero {len(Z)} (S_E range contains 0 at {sum(d['zero_in'] for d in Z)}); strictly inside {len(Q)} (S_E range contains 0 at {sum(d['zero_in'] for d in Q)}; dynamic ETF differs from one-review by > 1e-5 at {sum(d['moved'] for d in Q)})")
