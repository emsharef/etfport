"""Red's reproduction of experiment 047 (claim 044 against an exact two-review program), written from the registered Design
without reading experiments/047/run.py or the d16 harness. M7 finite law, N = M = K = 1, T = 2, beta = 1, gamma = 5,
Sigma_E = 0, no ETF cap, b_E = 1; theta four atoms (lam_bar +- s_lam, alpha_bar +- s_alpha), shocks four atoms
(+-sigma_f, +-sigma_A, 0): 16 states tomorrow. Own draws (seed (2047, i) in red's own order), so counts are compared as
rates. Part 2 and part 3(c)'s test are decided by the Design's linear feasibility problem in (eta_0, eta_1, sigma_0, sigma_1)."""
import sys, itertools, numpy as np, cvxpy as cp, warnings
from multiprocessing import Pool
warnings.simplefilter('ignore'); GAM, BETA, BP, BE = 5.0, 1.0, 1e4, 1.0
SOLV = dict(solver=cp.CLARABEL, tol_gap_abs=1e-12, tol_gap_rel=1e-12, tol_feas=1e-12, max_iter=500)
SLACK = 1e-6                                                   # Deviation 1: slack below this reads as binding


def moments(lh, ah, pl, pa, I):
    s = I['sf'] ** 2 + pl; mu = np.array([I['bA'] * lh + ah, BE * lh - I['cE']])
    S = np.array([[I['bA'] ** 2 * s + I['sA'] ** 2 + pa, I['bA'] * BE * s], [I['bA'] * BE * s, BE ** 2 * s]]); return mu, S


def inst(seed, costless=False):
    r = np.random.default_rng([2047, seed + (10000 if costless else 0)]); U = r.uniform
    I = dict(bA=U(0.5, 1.5), lb=U(-0.01, 0.03), ab=U(-0.01, 0.01), sl=U(0.001, 0.01), sa=U(0.0005, 0.004), sf=0.08)
    I['sA'] = 0.02 * np.sqrt(1 + U(0.01, 3)); I['kp'] = np.array([U(0, 0.02), U(0, 0.005)]); I['km'] = np.array([U(0, 0.02), U(0, 0.005)])
    if costless: I['kp'][1] = I['km'][1] = 0.0
    I['cE'] = U(0, 0.002); I['cap'] = r.choice([0.25, 1.0]); a = U(0, I['cap']); p = 0.0 if U() < 0.5 else U(0, 0.5); I['x0'] = np.array([a, p])
    pl0, pa0 = I['sl'] ** 2, I['sa'] ** 2; kl, ka = pl0 / (pl0 + I['sf'] ** 2), pa0 / (pa0 + I['sA'] ** 2)
    I['m0'] = moments(I['lb'], I['ab'], pl0, pa0, I); I['Z'] = []
    for (dl, da), (zf, za) in itertools.product(itertools.product([-1, 1], [-1, 1]), itertools.product([-1, 1], [-1, 1])):
        lam, al = I['lb'] + dl * I['sl'], I['ab'] + da * I['sa']; f = lam + zf * I['sf']; res = al + za * I['sA']
        lh, ah = I['lb'] + kl * (f - I['lb']), I['ab'] + ka * (res - I['ab'])
        I['Z'].append(dict(q=1 / 16, g=np.array([1 + I['bA'] * f + res, 1 + BE * f - I['cE']]), m=moments(lh, ah, (1 - kl) * pl0, (1 - ka) * pa0, I)))
    I['h'] = 10.0; x0, X1, *_ = joint(I, budget=False)
    sp0 = spend(x0, I['x0'], I); need = max(0.0, max(sp0 + spend(x1, z['g'] * x0, I) for z, x1 in zip(I['Z'], X1)))
    I['h'] = max(need * U(0.2, 1.2), 1e-3); return I


def spend(x, xm, I): d = x - xm; return d.sum() + I['kp'] @ np.maximum(d, 0) + I['km'] @ np.maximum(-d, 0)


def box(x, I):
    c = [x >= 0, x[0] <= I['cap']]; return c


def joint(I, budget=True):
    x0 = cp.Variable(2); u0 = cp.Variable(2, nonneg=True); d0 = cp.Variable(2, nonneg=True); c0 = I['kp'] @ u0 + I['km'] @ d0
    h0 = I['h'] - cp.sum(x0 - I['x0']) - c0; mu0, S0 = I['m0']
    cons = [x0 - I['x0'] == u0 - d0] + box(x0, I); b0 = h0 >= 0
    if budget: cons.append(b0)
    obj = mu0 @ x0 - GAM / 2 * cp.sum_squares(np.linalg.cholesky(S0).T @ x0) - c0; X1 = []; bs = []
    for z in I['Z']:
        x1 = cp.Variable(2); u = cp.Variable(2, nonneg=True); d = cp.Variable(2, nonneg=True); c1 = I['kp'] @ u + I['km'] @ d; mu, S = z['m']
        cons += [x1 - cp.multiply(z['g'], x0) == u - d] + box(x1, I); b = h0 - cp.sum(x1 - cp.multiply(z['g'], x0)) - c1 >= 0
        if budget: cons.append(b)
        bs.append(b); X1.append(x1); obj = obj + BETA * z['q'] * (mu @ x1 - GAM / 2 * cp.sum_squares(np.linalg.cholesky(S).T @ x1) - c1)
    pr = cp.Problem(cp.Maximize(BP * obj), cons); pr.solve(**SOLV)
    if not budget: return x0.value, [x.value for x in X1]
    e0 = float(b0.dual_value) / BP; e1 = [float(b.dual_value) / BP / (BETA * z['q']) for b, z in zip(bs, I['Z'])]
    return x0.value, [x.value for x in X1], e0, e1


def one_review(mu, S, xm, h, I):
    x = cp.Variable(2); u = cp.Variable(2, nonneg=True); d = cp.Variable(2, nonneg=True); c = I['kp'] @ u + I['km'] @ d
    b = h - cp.sum(x - xm) - c >= 0
    pr = cp.Problem(cp.Maximize(BP * (mu @ x - GAM / 2 * cp.sum_squares(np.linalg.cholesky(S).T @ x) - c)), [x - xm == u - d, b] + box(x, I)); pr.solve(**SOLV)
    return x.value, float(b.dual_value) / BP


def status(x, xm, cap, i, tol=1e-7):
    d = x[i] - xm[i]; atz = x[i] <= tol; atc = (i == 0 and x[i] >= cap - tol)
    return ('buy' if d > tol else 'sell' if d < -tol else 'hold'), atz, atc


def lines_lp(I, x0, X1, objective=None):
    """part 2's lines as an LP in (eta_0, eta_1(z), sig_0 = (1 + eta_hat) t_0, sig_1(z) = (1 + eta_1) t_1); returns (largest
    violation, eta_0 range) with the complementarity threshold SLACK."""
    n = len(I['Z']); e0 = cp.Variable(nonneg=True); e1 = cp.Variable(n, nonneg=True); s0 = cp.Variable(2); s1 = cp.Variable((n, 2)); v = cp.Variable(nonneg=True)
    eh = e0 + BETA * sum(z['q'] * e1[k] for k, z in enumerate(I['Z'])); cons = []
    h0 = I['h'] - spend(x0, I['x0'], I)
    if h0 > SLACK: cons.append(e0 == 0)
    def line(expr, sg, x, xm, kpi, kmi, e, i):
        st, atz, atc = status(x, xm, I['cap'], i); c = []
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
        xm = z['g'] * x0; mu, S = z['m']; g1 = mu - GAM * S @ x1
        if I['h'] - spend(x0, I['x0'], I) - spend(x1, xm, I) > SLACK: cons.append(e1[k] == 0)
        for i in range(2):
            cons += line(g1[i] - e1[k] - s1[k, i], s1[k, i], x1, xm, I['kp'][i], I['km'][i], e1[k], i)
            Ssum[i] = Ssum[i] + BETA * z['q'] * z['g'][i] * (e1[k] + s1[k, i])
    mu0, S0 = I['m0']; g0 = mu0 - GAM * S0 @ x0
    for i in range(2): cons += line(g0[i] + Ssum[i] - eh - s0[i], s0[i], x0, I['x0'], I['kp'][i], I['km'][i], eh, i)
    pr = cp.Problem(cp.Minimize(v), cons); pr.solve(solver=cp.CLARABEL); viol = v.value
    rng = None
    if objective == 'range':
        lo = cp.Problem(cp.Minimize(e0), cons + [v <= viol + 1e-9]); lo.solve(solver=cp.CLARABEL); a = e0.value
        hi = cp.Problem(cp.Maximize(e0), cons + [v <= viol + 1e-9, e0 <= 1]); hi.solve(solver=cp.CLARABEL); rng = (a, e0.value)
    return viol, rng


def svals(I, x0, X1, e1, j):
    """S_j from pinned tomorrow regimes (None if some state holds j at a bound)."""
    S = 0.0
    for z, x1, e in zip(I['Z'], X1, e1):
        xm = z['g'] * x0; st, atz, atc = status(x1, xm, I['cap'], j); mu, Sg = z['m']
        if st == 'buy': s = e + (1 + e) * I['kp'][j]
        elif st == 'sell': s = e - (1 + e) * I['km'][j]
        elif not atz and not atc: s = (mu - GAM * Sg @ x1)[j]
        else: return None
        S += BETA * z['q'] * z['g'][j] * s
    return S


def job(arg):
    seed, costless = arg; I = inst(seed, costless)
    x0, X1, e0, e1 = joint(I); h0 = I['h'] - spend(x0, I['x0'], I); h1 = [h0 - spend(x1, z['g'] * x0, I) for z, x1 in zip(I['Z'], X1)]
    # knife edges: holdings within 1e-6 of a trade or box boundary; a budget within 1e-7 of binding with multiplier < 1e-7
    knife = any(1e-7 < abs(x0[i] - I['x0'][i]) < 1e-6 or 1e-7 < x0[i] < 1e-6 or (i == 0 and 1e-7 < I['cap'] - x0[i] < 1e-6) for i in range(2))
    knife |= any(1e-7 < hh < 1e-6 or (hh <= 1e-7 and e < 1e-7) for hh, e in zip([h0] + h1, [e0] + e1))
    slack_bind = max([hh for hh, e in zip([h0] + h1, [e0] + e1) if e > 1e-6], default=0.0)          # Deviation 1
    b0 = h0 <= SLACK; b1 = any(hh <= SLACK for hh in h1)
    viol, rng = lines_lp(I, x0, X1, 'range' if (b0 and b1) else None)
    # 3(b): S_i bounds and the necessary conditions, at the solver's duals
    eh = e0 + BETA * np.mean(e1); mu0, S0 = I['m0']; g0 = mu0 - GAM * S0 @ x0; b3 = 0.0
    for i in range(2):
        Si = svals(I, x0, X1, e1, i)
        lo = BETA * sum(z['q'] * z['g'][i] * (e - (1 + e) * I['km'][i]) for z, e in zip(I['Z'], e1)); hi = BETA * sum(z['q'] * z['g'][i] * (e + (1 + e) * I['kp'][i]) for z, e in zip(I['Z'], e1))
        if Si is not None: b3 = max(b3, lo - Si, Si - hi)
        st, _, _ = status(x0, I['x0'], I['cap'], i)
        if st == 'buy': b3 = max(b3, eh + (1 + eh) * I['kp'][i] - hi - g0[i])
        if st == 'sell': b3 = max(b3, g0[i] - (eh - (1 + eh) * I['km'][i] - lo))
    # 4(a): the root one-review problem with shifted inputs at the fixed eta_hat (claim 110's object)
    Sv = [svals(I, x0, X1, e1, i) for i in range(2)]; a4 = None
    if all(s is not None for s in Sv):
        x = cp.Variable(2); u = cp.Variable(2, nonneg=True); d = cp.Variable(2, nonneg=True)
        pr = cp.Problem(cp.Maximize(BP * ((mu0 + np.array(Sv)) @ x - GAM / 2 * cp.sum_squares(np.linalg.cholesky(S0).T @ x) - (1 + eh) * (I['kp'] @ u + I['km'] @ d) - eh * cp.sum(x - I['x0']))), [x - I['x0'] == u - d] + box(x, I)); pr.solve(**SOLV)
        a4 = np.abs(x.value - x0).max()
    # 3(c): myopic policy, the test (LP at the myopic root with its own tomorrow solutions), and the sign
    xm0, em0 = one_review(mu0, S0, I['x0'], I['h'], I); hm = I['h'] - spend(xm0, I['x0'], I)
    Xm1, Em1 = zip(*[one_review(*z['m'], z['g'] * xm0, hm, I) for z in I['Z']])
    Im = dict(I); tv, _ = lines_lp(I, xm0, list(Xm1)); test = tv <= 1e-6; opt = np.abs(xm0 - x0).max() <= 1e-5
    signs = []
    for j in range(2):
        st, atz, atc = status(xm0, I['x0'], I['cap'], j)
        if st == 'buy' and not atz and not atc and not opt:
            Sj = svals(I, xm0, list(Xm1), list(Em1), j)
            if Sj is None: continue
            r = Sj - BETA * np.mean(Em1) * (1 + I['kp'][j]); dj = x0[j] - xm0[j]; do = x0[1 - j] - xm0[1 - j]
            if abs(r) > 1e-9 and abs(dj) > 1e-5: signs.append((j, r, dj, do, b0 or b1 or hm <= SLACK or any(e > 1e-7 for e in Em1), hm > SLACK))
    # 4(d): costless ETF held interior at the root
    d4 = None
    if costless and x0[1] > 1e-6:                   # held strictly inside its box (no ETF cap); kappa_E = 0 pins s_E = eta_1 in every regime
        SEdef = BETA * np.mean([z['g'][1] * e for z, e in zip(I['Z'], e1)]); SE = svals(I, x0, X1, e1, 1)
        d4 = (abs(SE - SEdef) if SE is not None else 0.0, abs(g0[1] - (eh - SEdef)))
    return dict(seed=seed, costless=costless, knife=knife, b0=b0, b1=b1, viol=viol, rng=rng, slack_bind=slack_bind, b3=b3, a4=a4, test=test, opt=opt, tv=tv, signs=signs, d4=d4)


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    with Pool(9) as p: O = p.map(job, [(i, False) for i in range(n)] + [(i, True) for i in range(n // 5)])
    for cl in (False, True):
        R = [o for o in O if o['costless'] == cl]; K = [o for o in R if not o['knife']]
        print(f"{'costless' if cl else 'main'}: {len(R)} instances, {len(R) - len(K)} knife edges; binds today {sum(o['b0'] for o in K)}, tomorrow {sum(o['b1'] for o in K)}, both {sum(o['b0'] and o['b1'] for o in K)}")
        print(f"  part 2: largest LP violation {max(o['viol'] for o in K):.1e}; 3(b) worst {max(o['b3'] for o in K):.1e}; 4(a) worst {max((o['a4'] for o in K if o['a4'] is not None), default=np.nan):.1e} at {sum(o['a4'] is not None for o in K)}")
        rg = [o['rng'][1] - o['rng'][0] for o in K if o['rng'] is not None]
        print(f"  Deviation 2: both bind at {len(rg)}; eta_0 range width > 1e-6 at {sum(w > 1e-6 for w in rg)}, max {max(rg, default=0):.1e}")
        print(f"  Deviation 1: largest slack at a multiplier > 1e-6: {max(o['slack_bind'] for o in R):.1e}")
        print(f"  3(c) test: optimal {sum(o['opt'] for o in K)}, not {sum(not o['opt'] for o in K)}; agree {sum(o['test'] == o['opt'] for o in K)} of {len(K)}; misses {[(o['seed'], round(o['tv'], 9)) for o in K if o['test'] != o['opt']]}")
        S = [(o['seed'], s) for o in K for s in o['signs']]; F = [(sd, s) for sd, s in S if np.sign(s[1]) != np.sign(s[2])]
        print(f"  sign rule: {len(S)} cases, {len(F)} fail; failures with the other instrument opposite and larger: {sum(np.sign(s[3]) == -np.sign(s[2]) and abs(s[3]) > abs(s[2]) for _, s in F)}; failures without any binding budget {sum(not s[4] for _, s in F)}")
        T = [(sd, s) for sd, s in S if s[5]]; print(f"  sign rule with today's budget slack at the myopic root (claim 044 as approved): {len(T)} cases, {sum(np.sign(s[1]) != np.sign(s[2]) for _, s in T)} fail")
        for sd, s in F: print(f"    {sd} {'fund' if s[0] == 0 else 'ETF'} resid {s[1]:+.1e} d_own {s[2]:+.1e} d_other {s[3]:+.1e} budget {s[4]} today-slack {s[5]}")
        if cl: D = [o['d4'] for o in K if o['d4'] is not None]; print(f"  4(d): {len(D)} held interior; S_E err {max((d[0] for d in D), default=0):.1e}, line err {max((d[1] for d in D), default=0):.1e}")
