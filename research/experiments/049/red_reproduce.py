"""Red's reproduction of experiment 049 (claim 045/046's bounds), written from the registered Design without reading
experiments/049/run.py or its addenda's scripts. Instances are rebuilt from experiment 047's seeds (2047, 0|1, i) in red's own
solver (red's experiment 047 red_reproduce.py, directory argument 1), so counts compare one for one; experiment 048's cells from
red's experiment 048 script (directory argument 2). Run: uv run python experiments/049/red_reproduce.py experiments/047 experiments/048 Checks: part 1's joint LPs; part 3's myopic-optimal interior trades and whether the
equation S_i = beta E[eta_1](1 + kappa^+_i) holds for some admissible tomorrow family; part 4 on 3,000 frictionless-ETF draws
(Deviation 2) with R^red_A - rho_0 R^red_E's range at the reduced point. Part 2's LP extremes are not re-run."""
import sys, itertools, numpy as np, cvxpy as cp, warnings
sys.path.insert(0, sys.argv[1])
from multiprocessing import Pool
import red_reproduce as R
import importlib.util


def load048():
    sp = importlib.util.spec_from_file_location('red048', sys.argv[2] + '/red_reproduce.py'); m = importlib.util.module_from_spec(sp); sp.loader.exec_module(m); return m
warnings.simplefilter('ignore'); TOLV = 1e-7


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


def parts123(arg):
    kind, k = arg
    if kind == 'main': I = analyst_instance(k)
    else:
        I = load048().build(*k)
    x0, X1, e0, e1 = R.joint(I); h0 = I['h'] - R.spend(x0, I['x0'], I); eb, nd = etabar_need(I, x0)
    knife = any(1e-7 < abs(x0[i] - I['x0'][i]) < 1e-6 or 1e-7 < x0[i] < 1e-6 for i in range(2)) or R.lines_lp(I, x0, X1)[0] > 1e-6
    # part 1: the selection eta_1 <= eta_bar jointly with today's lines (via the joint line LP) and eta_1 = 0 where need is covered
    v1 = lines_with(I, x0, X1, lambda E0, E1: [E1[j] <= eb[j] + 1e-9 for j in range(16)])
    v1b = lines_with(I, x0, X1, lambda E0, E1: [E1[j] == 0 for j in range(16) if h0 >= nd[j]])
    # part 3
    mu0, S0 = I['m0']; xm0, em0 = R.one_review(mu0, S0, I['x0'], I['h'], I); hm = I['h'] - R.spend(xm0, I['x0'], I)
    Xm1 = [R.one_review(*z['m'], z['g'] * xm0, max(hm, 0), I)[0] for z in I['Z']]; opt = np.abs(xm0 - x0).max() <= 1e-5
    inter = [i for i in range(2) if R.status(xm0, I['x0'], I['cap'], i)[0] != 'hold' and not any(R.status(xm0, I['x0'], I['cap'], i)[1:])]
    eq = None
    if opt and inter:
        e1v, s1v, cons, S, Ee = tomorrow_set(I, xm0, Xm1, max(hm, 0)); eq = []
        for i in inter:
            buy = xm0[i] > I['x0'][i]; r = S[i] - Ee * ((1 + I['kp'][i]) if buy else (1 - I['km'][i])); lo, hi = rng_of(r, cons)
            eq.append(lo <= 1e-7 and hi >= -1e-7)
    return dict(kind=kind, k=k, knife=knife, v1=v1, v1b=v1b, cover=all(h0 >= nd), opt=opt, inter=bool(inter), bind0=hm <= R.SLACK, eq=eq)


# part 1: experiment 047's line LP (red's), with extra constraints on (eta_0, eta_1)
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


def lines_with(I, x0, X1, extra): return lines_lp_extra(I, x0, X1, extra=extra)[0]


def part4(i):
    try: return _part4(i)
    except cp.error.SolverError: return dict(i=i, fail=True)


def _part4(i):
    I = analyst_instance(i, costless=True); mu0, S0 = I['m0']
    xm0, em0 = R.one_review(mu0, S0, I['x0'], I['h'], I); hm = I['h'] - R.spend(xm0, I['x0'], I)
    if not (xm0[0] > I['x0'][0] + 1e-6 and xm0[0] < I['cap'] - 1e-6 and hm > R.SLACK): return None
    x0, X1, e0, e1 = R.joint(I); xr, Xr = joint_fixA(I, xm0[0]); hr = I['h'] - R.spend(xr, I['x0'], I)
    if not (hr > R.SLACK and xr[1] > 1e-6 and x0[1] > 1e-6): return None
    e1v, s1v, cons, S, Ee = tomorrow_set(I, xr, Xr, hr); g0 = mu0 - R.GAM * S0 @ xr; rho = S0[0, 1] / S0[1, 1]
    cons = cons + [g0[1] + S[1] - Ee <= 1e-7, g0[1] + S[1] - Ee >= -1e-7]              # the ETF's root line at the reduced point (eta_0 = 0)
    val = (S[0] - Ee * (1 + I['kp'][0])) - rho * (S[1] - Ee)                               # R^red_A - rho_0 R^red_E
    lo, hi = rng_of(val, cons); d = x0[0] - xm0[0]
    return dict(i=i, lo=lo, hi=hi, d=d)


def report123(O):
    for kind in ('main', 'cell'):
        K = [o for o in O if o['kind'] == kind and not o['knife']]
        print(f"{kind}: {len(K)} after knife edges; part 1: eta_1 <= eta_bar jointly feasible at {sum(o['v1'] <= 1e-6 for o in K)}, eta_1 = 0 where covered at {sum(o['v1b'] <= 1e-6 for o in K)}; all states covered at {sum(o['cover'] for o in K)}")
        Q = [o for o in K if o['opt'] and o['inter']]; fails = [o['k'] for o in Q if not all(o['eq'])]
        print(f"  part 3: myopic optimal with an interior trade {len(Q)}, today's budget binding at {sum(o['bind0'] for o in Q)}; equation holds for some admissible family at {len(Q) - len(fails)}, fails at {len(fails)}: {fails}")


if __name__ == "__main__":
    E = load048()
    cells = list(itertools.product(E.PRE, E.STARTS, [0.005, 1.0], [1, 3], [0.2, 1, 5]))
    with Pool(9) as p:
        O = p.map(parts123, [('main', i) for i in range(300)] + [('cell', c) for c in cells])
        report123(O)
        P = [o for o in p.map(part4, range(3000)) if o is not None]
    F = [o['i'] for o in P if o.get('fail')]; P = [o for o in P if not o.get('fail')]
    print(f"part 4: solver failures (counted, set aside) {len(F)}: {F}")
    dec = [o for o in P if np.sign(o['lo']) == np.sign(o['hi']) and abs(o['d']) > 1e-5]
    print(f"part 4: {len(P)} of 3,000 draws meet the hypotheses; range excludes zero at {sum(np.sign(o['lo']) == np.sign(o['hi']) for o in P)}; sign = sign(a_dyn - a_my) at {sum(np.sign(o['lo']) == np.sign(o['d']) for o in dec)} of {len(dec)} "
          f"({sum(o['d'] > 0 for o in dec)} front-loading, {sum(o['d'] < 0 for o in dec)} hoarding); draws {[o['i'] for o in P]}")
