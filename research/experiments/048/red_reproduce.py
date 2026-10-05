"""Red's reproduction of experiment 048 (D18), written from the registered Design without reading experiments/048/run.py or
the d16 harness. M8 finite law: b_A = b_E = 1, gamma = 5, beta = 1, c^E = 0, sigma_E = 0, fund cap 0.25, no ETF cap; theta four
atoms m_0 +- sqrt(P_0), shocks (+-sigma_f, +-sigma_A): 16 states tomorrow. Policies: dynamic (the lifted joint program), myopic
(one-review at each review), exposure-first (claim 111's stage 1 with the fund frozen at its incumbent, clipped to the box as
PM's cap fix says, then claim 104's fibre stage 2, at each review). Claim 041's side stage is not reproduced.
Argument 1: a directory holding red's experiment 047 red_reproduce.py (its joint, one-review and line-LP solvers)."""
import sys, itertools, numpy as np, cvxpy as cp, warnings
sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else '.')
import red_reproduce as R
warnings.simplefilter('ignore'); GAM, BP = 5.0, 1e4
PRE = {"equity-style": dict(alpha=-0.0019, fund=0.0050, etf=0.0002), "fixed-income-style": dict(alpha=0.0020, fund=0.0020, etf=0.0050)}
STARTS = {"all-ETF": (0.0, 0.9), "all-fund": (0.15, 0.0), "mixed": (0.075, 0.45)}


def build(regime, start, cash, pk, ck):
    P = PRE[regime]; I = dict(bA=1.0, sf=0.08, sA=0.02, cE=0.0, cap=0.25, x0=np.array(STARTS[start]), h=cash)
    kf = P['fund'] * ck; I['kp'] = np.array([kf, P['etf']]); I['km'] = I['kp'].copy()
    lb, ab, sl, sa = 0.015, P['alpha'], 0.005 * pk, 0.0035 * pk; pl0, pa0 = sl ** 2, sa ** 2
    kl, ka = pl0 / (pl0 + I['sf'] ** 2), pa0 / (pa0 + I['sA'] ** 2); I['m0'] = R.moments(lb, ab, pl0, pa0, I); I['Z'] = []
    for (dl, da), (zf, za) in itertools.product(itertools.product([-1, 1], [-1, 1]), itertools.product([-1, 1], [-1, 1])):
        lam, al = lb + dl * sl, ab + da * sa; f = lam + zf * I['sf']; res = al + za * I['sA']
        I['Z'].append(dict(q=1 / 16, g=np.array([1 + f + res, 1 + f]), m=R.moments(lb + kl * (f - lb), ab + ka * (res - ab), (1 - kl) * pl0, (1 - ka) * pa0, I)))
    return I


def score(mu, S, x, xm, I): d = x - xm; return mu @ x - GAM / 2 * x @ S @ x - I['kp'] @ np.maximum(d, 0) - I['km'] @ np.maximum(-d, 0)


def solve(mu, S, xm, h, I, fix_a=None, fibre=None):
    x = cp.Variable(2); u = cp.Variable(2, nonneg=True); d = cp.Variable(2, nonneg=True); c = I['kp'] @ u + I['km'] @ d
    cons = [x - xm == u - d, x >= 0, x[0] <= I['cap'], h - cp.sum(x - xm) - c >= 0]
    if fix_a is not None: cons.append(x[0] == fix_a)
    if fibre is not None: cons.append(x[0] + x[1] == fibre)
    pr = cp.Problem(cp.Maximize(BP * (mu @ x - GAM / 2 * cp.sum_squares(np.linalg.cholesky(S).T @ x) - c)), cons)
    try: pr.solve(**R.SOLV)
    except Exception: pass
    if x.value is None or pr.status not in ('optimal', 'optimal_inaccurate'):
        try: pr.solve()
        except Exception: pass
    return None if x.value is None or pr.status not in ('optimal', 'optimal_inaccurate') else x.value


def expo_first(mu, S, xm, h, I, clip=True):
    """claim 111's stage 1 (fund frozen at its incumbent; clipped to the box under PM's fix), then claim 104's fibre stage 2."""
    af = min(xm[0], I['cap']) if clip else xm[0]
    if af > I['cap'] + 1e-12: return None, 'undefined'
    x1 = solve(mu, S, xm, h, I, fix_a=af)
    if x1 is None: return None, 'stage1-fail'
    x2 = solve(mu, S, xm, h, I, fibre=x1[0] + x1[1])
    if x2 is None: return x1, 'fallback'                     # the one-point fibre (Deviation 2)
    return x2, 'ok'


def policy_value(I, root, tomorrow):
    mu0, S0 = I['m0']; x0, info = root(mu0, S0, I['x0'], I['h'])
    if x0 is None: return None, None, info
    h0 = max(I['h'] - R.spend(x0, I['x0'], I), 0.0); v = score(mu0, S0, x0, I['x0'], I); X1 = []
    for z in I['Z']:
        x1, inf = tomorrow(*z['m'], z['g'] * x0, h0)
        if x1 is None: return None, None, inf
        info = info if info != 'ok' else inf; v += z['q'] * score(*z['m'], x1, z['g'] * x0, I); X1.append(x1)
    return v, (x0, X1), info


def cell(args):
    regime, start, cash, pk, ck = args; I = build(*args); mu0, S0 = I['m0']
    x0, X1, e0, e1 = R.joint(I); vd = score(mu0, S0, x0, I['x0'], I) + sum(z['q'] * score(*z['m'], x1, z['g'] * x0, I) for z, x1 in zip(I['Z'], X1))
    h0 = I['h'] - R.spend(x0, I['x0'], I); binds = (h0 <= 1e-6 and e0 > 1e-7) or any(h0 - R.spend(x1, z['g'] * x0, I) <= 1e-6 and e > 1e-7 for z, x1, e in zip(I['Z'], X1, e1))
    my = lambda mu, S, xm, h: (R.one_review(mu, S, xm, h, I)[0], 'ok')
    vm, (xm0, Xm1), _ = policy_value(I, my, my)
    opt = np.abs(xm0 - x0).max() <= 1e-5 and np.abs(np.mean([z['g'] * 0 + x for z, x in zip(I['Z'], Xm1)], 0) - np.mean(X1, 0)).max() <= 1e-5
    test = R.lines_lp(I, xm0, list(Xm1))[0] <= 1e-6
    ef = lambda mu, S, xm, h: expo_first(mu, S, xm, h, I)
    ve, _, infe = policy_value(I, ef, ef)
    efo = lambda mu, S, xm, h: expo_first(mu, S, xm, h, I, clip=False)
    _, _, info_orig = policy_value(I, efo, efo)
    over_cap = sum(z['g'][0] * x0[0] > I['cap'] + 1e-12 for z in I['Z'])     # states where marking carries the dynamic fund above its cap
    return dict(cell=args, vd=vd, lm=(vd - vm) * 1e4, le=None if ve is None else (vd - ve) * 1e4, infe=infe, orig=info_orig, binds=binds, opt=opt, test=test,
                x0=x0, xm0=xm0, e0=e0, Ee1=np.mean(e1), over_cap=over_cap)


if __name__ == "__main__":
    from multiprocessing import Pool
    grid = list(itertools.product(PRE, STARTS, [0.005, 1.0], [1, 3], [0.2, 1, 5]))
    with Pool(9) as p: O = p.map(cell, grid)
    lm = np.array([o['lm'] for o in O]); le = [o['le'] for o in O if o['le'] is not None]
    print(f"72 cells. myopic: works well (< 0.01 bp) {np.sum(lm < 0.01)}, median {np.median(lm):.4f} bp, max {lm.max():.2f} bp, min {lm.min():.1e}")
    print(f"exposure-first (cap fix): defined {len(le)}, works well {sum(l < 0.01 for l in le)}, median {np.median(le):.4f}, max {max(le):.2f} bp; fallbacks {sum(o['infe'] == 'fallback' for o in O)}; "
          f"undefined under the original freeze {sum(o['orig'] == 'undefined' for o in O)}")
    print(f"claim 044's test vs myopic optimal (holdings, 1e-5): agree {sum(o['test'] == o['opt'] for o in O)} of 72 ({sum(o['opt'] for o in O)} optimal)")
    print(f"budget binds (dynamic): {sum(o['binds'] for o in O)} cells")
    print("regime | start | cash | myopic max, works well | expo-first max, works well | binds | myopic optimal")
    for rg, st, ca in itertools.product(PRE, STARTS, [0.005, 1.0]):
        C = [o for o in O if o['cell'][:3] == (rg, st, ca)]; E = [o['le'] for o in C if o['le'] is not None]
        print(f"{rg} | {st} | {'tight' if ca < 0.5 else 'slack'} | {max(o['lm'] for o in C):.3f}, {sum(o['lm'] < 0.01 for o in C)}/6 | {max(E):.3f}, {sum(e < 0.01 for e in E)}/{len(E)}"
              f"{'' if all(o['orig'] != 'undefined' for o in C) else ' (orig undefined ' + str(sum(o['orig'] == 'undefined' for o in C)) + ')'} | {sum(o['binds'] for o in C)}/6 | {sum(o['opt'] for o in C)}/6")
    L = [o for o in O if o['lm'] > 0.01]
    print("myopic loss cells:", [(o['cell'][0][:5], o['cell'][1], o['cell'][3], o['cell'][4], round(o['lm'], 2), o['x0'].round(3).tolist(), o['xm0'].round(3).tolist(), f"{o['Ee1']:.0e}") for o in L][:6])
