"""Red's reproduction of experiment 053 (D21: claim 047's rule against the dynamic optimum and the repeated one-review policy),
written from the registered Design without reading experiments/053/run.py or the harness. M8 finite law as in experiment 048
(b = 1, gamma = 5, beta = 1, c^E = 0, sigma_E = 0, fund cap 0.25, no ETF cap, 16 states), the 84-cell grid. The alpha revision
variance is scaled by changing the alpha prior variance p so that p^2/(p + sigma_A^2) is the preset's times the factor (the
premium's prior unchanged): red's reading of the Design's "revision-variance input". Also: the post hoc band variant (the
fixed-fund joint optimum), and the at-zero slope convention's effect. Run: uv run python experiments/053/red_reproduce.py experiments/047"""
import sys, itertools, numpy as np, cvxpy as cp, warnings
sys.path.insert(0, sys.argv[1])
from multiprocessing import Pool
import red_reproduce as R
warnings.simplefilter('ignore')
PRE = {"equity-style": dict(alpha=-0.0019, fund=0.0050, etf=0.0002), "fixed-income-style": dict(alpha=0.0020, fund=0.0020, etf=0.0050)}
STARTS = {"all-ETF": (0.0, 0.9), "all-fund": (0.15, 0.0), "mixed": (0.075, 0.45)}
SETTINGS = ["preset", "rev x0.25", "rev x4", "fund buy x0.5", "fund buy x2", "ETF sell x0.5", "ETF sell x2"]


def build(regime, start, cash, setting):
    P = PRE[regime]; I = dict(bA=1.0, sf=0.08, sA=0.02, cE=0.0, cap=0.25, x0=np.array(STARTS[start]), h=cash)
    I['kp'] = np.array([P['fund'], P['etf']]); I['km'] = I['kp'].copy()
    if setting == "fund buy x0.5": I['kp'][0] *= 0.5
    if setting == "fund buy x2": I['kp'][0] *= 2
    if setting == "ETF sell x0.5": I['km'][1] *= 0.5
    if setting == "ETF sell x2": I['km'][1] *= 2
    lb, ab, sl = 0.015, P['alpha'], 0.005; pa = 0.0035 ** 2; sA2 = I['sA'] ** 2
    if setting.startswith("rev"):
        c = 0.25 if "0.25" in setting else 4.0; v0 = pa ** 2 / (pa + sA2); cv = c * v0; pa = (cv + np.sqrt(cv ** 2 + 4 * cv * sA2)) / 2
    sa = np.sqrt(pa); pl0 = sl ** 2; kl, ka = pl0 / (pl0 + I['sf'] ** 2), pa / (pa + sA2)
    I['m0'] = R.moments(lb, ab, pl0, pa, I); I['Z'] = []
    for (dl, da), (zf, za) in itertools.product(itertools.product([-1, 1], [-1, 1]), itertools.product([-1, 1], [-1, 1])):
        lam, al = lb + dl * sl, ab + da * sa; f = lam + zf * I['sf']; res = al + za * I['sA']
        I['Z'].append(dict(q=1 / 16, g=np.array([1 + f + res, 1 + f]), m=R.moments(lb + kl * (f - lb), ab + ka * (res - ab), (1 - kl) * pl0, (1 - ka) * pa, I)))
    return I


def score(mu, S, x, xm, I): d = x - xm; return mu @ x - R.GAM / 2 * x @ S @ x - I['kp'] @ np.maximum(d, 0) - I['km'] @ np.maximum(-d, 0)


def value_from_root(I, x0):
    """expected objective with root x0 and the one-review problem at review 1 (optimal at the last review)."""
    mu0, S0 = I['m0']; h0 = max(I['h'] - R.spend(x0, I['x0'], I), 0.0); v = score(mu0, S0, x0, I['x0'], I); X1 = []
    for z in I['Z']:
        x1, _ = R.one_review(*z['m'], z['g'] * x0, h0, I); X1.append(x1); v += R.BETA * z['q'] * score(*z['m'], x1, z['g'] * x0, I)
    return v, X1


def joint_fixA(I, a):
    x0 = cp.Variable(2); u0 = cp.Variable(2, nonneg=True); d0 = cp.Variable(2, nonneg=True); c0 = I['kp'] @ u0 + I['km'] @ d0; h0 = I['h'] - cp.sum(x0 - I['x0']) - c0
    mu0, S0 = I['m0']; cons = [x0 - I['x0'] == u0 - d0, x0 >= 0, x0[0] <= I['cap'], h0 >= 0, x0[0] == a]
    obj = mu0 @ x0 - R.GAM / 2 * cp.sum_squares(np.linalg.cholesky(S0).T @ x0) - c0
    for z in I['Z']:
        x1 = cp.Variable(2); u = cp.Variable(2, nonneg=True); d = cp.Variable(2, nonneg=True); c1 = I['kp'] @ u + I['km'] @ d; mu, S = z['m']
        cons += [x1 - cp.multiply(z['g'], x0) == u - d, x1 >= 0, x1[0] <= I['cap'], h0 - cp.sum(x1 - cp.multiply(z['g'], x0)) - c1 >= 0]
        obj = obj + R.BETA * z['q'] * (mu @ x1 - R.GAM / 2 * cp.sum_squares(np.linalg.cholesky(S).T @ x1) - c1)
    cp.Problem(cp.Maximize(R.BP * obj), cons).solve(**R.SOLV); return x0.value


def rule_root(I, xm0, X1m, at_zero='low'):
    """claim 047 part 3(b)'s registered rule: S_E from the one-review tomorrow, p = p^my + S_E/(gamma Sigma_EE), fund at a^my,
    moved toward p^my to the nearest feasible holding."""
    mu0, S0 = I['m0']; SE = 0.0
    for z, x1 in zip(I['Z'], X1m):
        xm = z['g'] * xm0; d = x1[1] - xm[1]; g1 = (z['m'][0] - R.GAM * z['m'][1] @ x1)[1]
        if d > 1e-7: t = I['kp'][1]
        elif d < -1e-7: t = -I['km'][1]
        elif x1[1] > 1e-7: t = g1
        else: t = max(g1, -I['km'][1]) if at_zero == 'low' else I['kp'][1]
        SE += R.BETA * z['q'] * z['g'][1] * t
    p = xm0[1] + SE / (R.GAM * S0[1, 1]); x = np.array([xm0[0], max(p, 0.0)])
    if R.spend(x, I['x0'], I) > I['h']:                                   # the budget: move toward p^my until feasible (bisection)
        lo, hi = xm0[1], x[1]
        for _ in range(60):
            mid = (lo + hi) / 2
            if R.spend(np.array([xm0[0], mid]), I['x0'], I) <= I['h']: lo = mid
            else: hi = mid
        x[1] = lo
    return x, SE


def cell(args):
    regime, start, cash, setting = args; I = build(*args); mu0, S0 = I['m0']
    x0, X1, e0, e1 = R.joint(I)
    vd = score(mu0, S0, x0, I['x0'], I) + sum(R.BETA * z['q'] * score(*z['m'], x1, z['g'] * x0, I) for z, x1 in zip(I['Z'], X1))
    xm0, _ = R.one_review(mu0, S0, I['x0'], I['h'], I); vm, X1m = value_from_root(I, xm0)
    xr, SE = rule_root(I, xm0, X1m); vr, _ = value_from_root(I, xr)
    xr2, _ = rule_root(I, xm0, X1m, at_zero='high'); vr2, _ = value_from_root(I, xr2)
    xb = joint_fixA(I, xm0[0]); vb, _ = value_from_root(I, xb)
    atzero = sum(abs(x1[1] - z['g'][1] * xm0[1]) <= 1e-7 and x1[1] <= 1e-7 for z, x1 in zip(I['Z'], X1m))
    return dict(cell=args, lm=(vd - vm) * 1e4, lr=(vd - vr) * 1e4, lr2=(vd - vr2) * 1e4, lb=(vd - vb) * 1e4,
                shift_dyn=x0[1] - xm0[1], shift_rule=xr[1] - xm0[1], fund_same=abs(x0[0] - xm0[0]) <= 1e-5, atzero=atzero)


if __name__ == "__main__":
    grid = list(itertools.product(PRE, STARTS, [1.0, 0.005], SETTINGS))
    with Pool(9) as p: O = p.map(cell, grid)
    lm = np.array([o['lm'] for o in O]); lr = np.array([o['lr'] for o in O]); lb = np.array([o['lb'] for o in O])
    print(f"84 cells: myopic works well {np.sum(lm < 0.01)}, largest {lm.max():.3f} bp; rule works well {np.sum(lr < 0.01)}, worse than myopic by > 0.01 bp {np.sum(lr > lm + 0.01)}, largest {lr.max():.3f} bp")
    M = lm > 0.01; rec = 1 - lr[M] / lm[M]
    print(f"recovery where myopic loses > 0.01 bp (n = {M.sum()}): median {np.median(rec):.3f} [{rec.min():.3f}, {rec.max():.3f}]")
    print(f"band variant (fixed-fund joint optimum): works well {np.sum(lb < 0.01)}, largest loss {lb.max():.1e} bp; dynamic fund = one-review fund at {sum(o['fund_same'] for o in O)} of 84")
    Z = [o for o in O if o['atzero'] > 0]
    print(f"at-zero convention: cells with the ETF held at zero in some one-review tomorrow state {len(Z)}; rule loss changes (upper end of the admissible slope) by at most {max((abs(o['lr2'] - o['lr']) for o in Z), default=0):.2e} bp")
    for o in O:
        if o['cell'] == ("fixed-income-style", "all-ETF", 1.0, "preset"):
            print(f"FI all-ETF preset: myopic {o['lm']:.3f} bp, rule {o['lr']:.3f} bp, shifts dynamic {o['shift_dyn']:+.4f}, rule {o['shift_rule']:+.4f}")
