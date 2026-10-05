"""Red's reproduction of experiment 054 (D21's literal rule on 144 new cells), written from the registered Design without reading
experiments/054/run.py or experiment 053's rule_band. M8 finite law as in experiments 048 and 053 (red's reading of the revision-
variance input, as in red's 053 reproduction). The literal rule: fund at a^my; the ETF solves today's banded line with S_E(p) read
from the one-review tomorrow at (a^my, p) and cash h(p); damped iteration p <- (p + line(S_E(p)))/2 from S_E = 0, step < 1e-8, at
most 60 iterations; the budget clip toward p^my. Also: the iteration from two other starting points, and the fixed-fund joint
optimum. Run: uv run python experiments/054/red_reproduce.py experiments/047"""
import sys, itertools, numpy as np, cvxpy as cp, warnings
sys.path.insert(0, sys.argv[1])
from multiprocessing import Pool
import red_reproduce as R
warnings.simplefilter('ignore')
PRE = {"equity-style": dict(alpha=-0.0019, fund=0.0050, etf=0.0002), "fixed-income-style": dict(alpha=0.0020, fund=0.0020, etf=0.0050)}
STARTS = [(0.05, 0.10), (0.05, 0.80), (0.22, 0.30), (0.10, 0.50)]


def build(regime, start, cash, rev, sale):
    P = PRE[regime]; I = dict(bA=1.0, sf=0.08, sA=0.02, cE=0.0, cap=0.25, x0=np.array(start), h=cash)
    I['kp'] = np.array([P['fund'], P['etf']]); I['km'] = I['kp'].copy(); I['km'][1] *= sale
    lb, ab, sl = 0.015, P['alpha'], 0.005; pa = 0.0035 ** 2; sA2 = I['sA'] ** 2
    v0 = pa ** 2 / (pa + sA2); cv = rev * v0; pa = (cv + np.sqrt(cv ** 2 + 4 * cv * sA2)) / 2
    sa = np.sqrt(pa); pl0 = sl ** 2; kl, ka = pl0 / (pl0 + I['sf'] ** 2), pa / (pa + sA2)
    I['m0'] = R.moments(lb, ab, pl0, pa, I); I['Z'] = []
    for (dl, da), (zf, za) in itertools.product(itertools.product([-1, 1], [-1, 1]), itertools.product([-1, 1], [-1, 1])):
        lam, al = lb + dl * sl, ab + da * sa; f = lam + zf * I['sf']; res = al + za * I['sA']
        I['Z'].append(dict(q=1 / 16, g=np.array([1 + f + res, 1 + f]), m=R.moments(lb + kl * (f - lb), ab + ka * (res - ab), (1 - kl) * pl0, (1 - ka) * pa, I)))
    return I


def score(mu, S, x, xm, I): d = x - xm; return mu @ x - R.GAM / 2 * x @ S @ x - I['kp'] @ np.maximum(d, 0) - I['km'] @ np.maximum(-d, 0)


def value_from_root(I, x0):
    mu0, S0 = I['m0']; h0 = max(I['h'] - R.spend(x0, I['x0'], I), 0.0); v = score(mu0, S0, x0, I['x0'], I)
    for z in I['Z']:
        x1, _ = R.one_review(*z['m'], z['g'] * x0, h0, I); v += R.BETA * z['q'] * score(*z['m'], x1, z['g'] * x0, I)
    return v


def joint_fixA(I, a):
    x0 = cp.Variable(2); u0 = cp.Variable(2, nonneg=True); d0 = cp.Variable(2, nonneg=True); c0 = I['kp'] @ u0 + I['km'] @ d0; h0 = I['h'] - cp.sum(x0 - I['x0']) - c0
    mu0, S0 = I['m0']; cons = [x0 - I['x0'] == u0 - d0, x0 >= 0, x0[0] <= I['cap'], h0 >= 0, x0[0] == a]
    obj = mu0 @ x0 - R.GAM / 2 * cp.sum_squares(np.linalg.cholesky(S0).T @ x0) - c0
    for z in I['Z']:
        x1 = cp.Variable(2); u = cp.Variable(2, nonneg=True); d = cp.Variable(2, nonneg=True); c1 = I['kp'] @ u + I['km'] @ d; mu, S = z['m']
        cons += [x1 - cp.multiply(z['g'], x0) == u - d, x1 >= 0, x1[0] <= I['cap'], h0 - cp.sum(x1 - cp.multiply(z['g'], x0)) - c1 >= 0]
        obj = obj + R.BETA * z['q'] * (mu @ x1 - R.GAM / 2 * cp.sum_squares(np.linalg.cholesky(S).T @ x1) - c1)
    cp.Problem(cp.Maximize(R.BP * obj), cons).solve(**R.SOLV); return x0.value


def S_E(I, a, p):
    x = np.array([a, p]); h = max(I['h'] - R.spend(x, I['x0'], I), 0.0); S = 0.0
    for z in I['Z']:
        xm = z['g'] * x; x1, _ = R.one_review(*z['m'], xm, h, I); d = x1[1] - xm[1]; g1 = (z['m'][0] - R.GAM * z['m'][1] @ x1)[1]
        t = I['kp'][1] if d > 1e-7 else (-I['km'][1] if d < -1e-7 else (g1 if x1[1] > 1e-7 else max(g1, -I['km'][1])))
        S += R.BETA * z['q'] * z['g'][1] * t
    return S


def line(I, a, S):
    """today's banded ETF line with the fund at a: g_{0,E}(p) + S = t_{0,E}(p); returns p (>= 0)."""
    mu0, S0 = I['m0']; p0 = I['x0'][1]; c = R.GAM * S0[1, 1]; g = mu0[1] - R.GAM * (S0[1, 0] * a + S0[1, 1] * p0) + S
    if g > I['kp'][1]: p = p0 + (g - I['kp'][1]) / c
    elif g < -I['km'][1]: p = p0 + (g + I['km'][1]) / c
    else: p = p0
    return max(p, 0.0)


def literal(I, a, p_start=None):
    p = line(I, a, 0.0) if p_start is None else p_start
    for it in range(1, 61):
        pn = (p + line(I, a, S_E(I, a, p))) / 2
        if abs(pn - p) < 1e-8: return pn, it, True
        p = pn
    return p, 60, False


def cell(args):
    I = build(*args); mu0, S0 = I['m0']
    x0, X1, e0, e1 = R.joint(I); vd = score(mu0, S0, x0, I['x0'], I) + sum(R.BETA * z['q'] * score(*z['m'], x1, z['g'] * x0, I) for z, x1 in zip(I['Z'], X1))
    h0 = I['h'] - R.spend(x0, I['x0'], I); slack = h0 > 1e-6 and all(h0 - R.spend(x1, z['g'] * x0, I) > 1e-6 for z, x1 in zip(I['Z'], X1))
    xm0, _ = R.one_review(mu0, S0, I['x0'], I['h'], I); vm = value_from_root(I, xm0)
    p, its, conv = literal(I, xm0[0]); x = np.array([xm0[0], p]); clipped = False
    if R.spend(x, I['x0'], I) > I['h']:
        clipped = True; lo, hi = 0.0, 1.0
        for _ in range(60):
            mid = (lo + hi) / 2; xx = xm0 + mid * (x - xm0)
            if R.spend(xx, I['x0'], I) <= I['h']: lo = mid
            else: hi = mid
        x = xm0 + lo * (x - xm0)
    vr = value_from_root(I, x)
    fund_gap = abs(x0[0] - xm0[0]); dom = slack and fund_gap <= 1e-5
    starts = None
    if dom:
        pa, _, ca = literal(I, xm0[0], 0.0); pb, _, cb = literal(I, xm0[0], xm0[1] + 0.3); pj = joint_fixA(I, xm0[0])[1]
        starts = dict(spread=max(abs(pa - p), abs(pb - p)), conv=ca and cb, joint=abs(pj - p))
    return dict(cell=args, dom=dom, slack=slack, fund_gap=fund_gap, lm=(vd - vm) * 1e4, lr=(vd - vr) * 1e4, gap=abs(x[1] - x0[1]), its=its, conv=conv,
                moved=abs(x0[1] - xm0[1]) > 1e-5, untraded=abs(xm0[1] - I['x0'][1]) <= 1e-7, clipped=clipped, starts=starts)


if __name__ == "__main__":
    grid = list(itertools.product(PRE, STARTS, [0.30, 0.02], [0.5, 2.0, 8.0], [0.75, 1.5, 3.0]))
    with Pool(9) as p: O = p.map(cell, grid)
    D = [o for o in O if o['dom']]; nb = sum(not o['slack'] for o in O); nf = sum(o['slack'] and o['fund_gap'] > 1e-5 for o in O)
    print(f"144 cells: domain {len(D)} (equity {sum(o['cell'][0][0] == 'e' for o in D)}, fixed-income {sum(o['cell'][0][0] == 'f' for o in D)}); budget binds {nb}; fund moves (budget slack) {nf}")
    fails = [o for o in D if not (o['conv'] and o['lr'] < 0.01 and o['gap'] < 1e-5)]
    print(f"domain: failures {len(fails)}; all converged {all(o['conv'] for o in D)}, max iterations {max(o['its'] for o in D)}; max loss {max(o['lr'] for o in D):.1e} bp; max ETF gap {max(o['gap'] for o in D):.1e}; clipped {sum(o['clipped'] for o in D)}")
    print(f"  force: dynamic ETF moved at {sum(o['moved'] for o in D)}; one-review ETF untraded at {sum(o['untraded'] for o in D)}; myopic not working well at {sum(o['lm'] >= 0.01 for o in D)}, max myopic loss {max(o['lm'] for o in D):.2f} bp")
    print(f"  starting points (0, p^my + 0.3): max spread of the fixed points {max(o['starts']['spread'] for o in D):.1e}, all converged {all(o['starts']['conv'] for o in D)}; max |rule - fixed-fund joint optimum| {max(o['starts']['joint'] for o in D):.1e}")
    F = [o for o in O if o['slack'] and o['fund_gap'] > 1e-5]
    if F: print(f"outside, fund moves: rule loss {min(o['lr'] for o in F):.2f} to {max(o['lr'] for o in F):.2f} bp")
    B = [o for o in O if not o['slack']]
    if B: print(f"outside, budget binds: myopic loss max {max(o['lm'] for o in B):.1e} bp, rule loss max {max(o['lr'] for o in B):.1e} bp")
