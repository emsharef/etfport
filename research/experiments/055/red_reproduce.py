"""Red's reproduction of experiment 055 (claim 113, several funds sharing one ETF), written from the registered Design without reading
experiments/055/run.py or experiments/d16-harness/harness_n.py. Two funds, one ETF, one factor, two reviews, two-point laws per
coordinate (8 parameter atoms x 8 shock atoms = 64 states), the 48 registered cells; red's own lifted joint program in
cvxpy/CLARABEL. Incumbent values are read both from the marking constraints' duals and from tomorrow's regimes. Random roots for
2(a) are red's own draws (seed 555), so 2(a)'s counts are compared as rates.
Run: uv run python experiments/055/red_reproduce.py"""
import itertools, numpy as np, cvxpy as cp, warnings
from multiprocessing import Pool
warnings.simplefilter('ignore'); GAM, BETA, BP = 5.0, 1.0, 1e4; NF = 2; n = 3
SOLV = dict(solver=cp.CLARABEL, tol_gap_abs=1e-12, tol_gap_rel=1e-12, tol_feas=1e-12, max_iter=500)
PRE = {"equity-style": dict(alpha=-0.0019, fund=0.0050, etf=0.0002), "fixed-income-style": dict(alpha=0.0020, fund=0.0020, etf=0.0050)}
STARTS = {"all-ETF": (0, 0, 0.9), "all-fund": (0.15, 0.15, 0), "fund-heavy": (0.22, 0.10, 0.30), "mixed": (0.05, 0.05, 0.5)}


def build(regime, start, cash, setting):
    P = PRE[regime]; b = np.array([1.0, 0.8, 1.0]); sf, sA = 0.08, np.array([0.02, 0.02]); lb, sl = 0.015, 0.005
    am = np.array([P['alpha'], P['alpha'] / 2]); pa = np.full(2, 0.0035 ** 2)
    if setting == "rev x4":
        v0 = pa ** 2 / (pa + sA ** 2); cv = 4 * v0; pa = (cv + np.sqrt(cv ** 2 + 4 * cv * sA ** 2)) / 2
    kp = np.array([P['fund'], P['fund'] * 1.5, P['etf']]); km = kp.copy()
    if setting == "ETF sale x3": km[2] *= 3
    pl = sl ** 2; kl = pl / (pl + sf ** 2); ka = pa / (pa + sA ** 2)
    def mom(lh, ah, pl_, pa_):
        s = sf ** 2 + pl_; mu = np.concatenate([b[:NF] * lh + ah, [b[2] * lh]])
        return mu, s * np.outer(b, b) + np.diag(np.concatenate([sA ** 2 + pa_, [0.0]]))
    I = dict(b=b, v=sA ** 2 + pa, sEE=b[2] ** 2 * (sf ** 2 + pl), kp=kp, km=km, cap=np.array([0.25, 0.25, np.inf]), x0=np.array(start, float), h=cash)
    I['m0'] = mom(lb, am, pl, pa); I['Z'] = []
    for sg in itertools.product([-1, 1], repeat=6):
        lam = lb + sg[0] * sl; al = am + np.array(sg[1:3]) * np.sqrt(pa); f = lam + sg[3] * sf; res = al + np.array(sg[4:6]) * sA
        lh = lb + kl * (f - lb); ah = am + ka * (res - am)
        I['Z'].append(dict(q=1 / 64, g=np.concatenate([1 + b[:NF] * f + res, [1 + f]]), m=mom(lh, ah, (1 - kl) * pl, (1 - ka) * pa)))
    return I


def spend(x, xm, I): d = x - xm; return d.sum() + I['kp'] @ np.maximum(d, 0) + I['km'] @ np.maximum(-d, 0)


def box(x, I): return [x >= 0, x[:NF] <= I['cap'][:NF]]


def review(mu, S, xm, h, I, budget=True):
    x = cp.Variable(n); u = cp.Variable(n, nonneg=True); d = cp.Variable(n, nonneg=True); c = I['kp'] @ u + I['km'] @ d
    cons = [x - xm == u - d] + box(x, I); b = h - cp.sum(x - xm) - c >= 0
    if budget: cons.append(b)
    cp.Problem(cp.Maximize(BP * (mu @ x - GAM / 2 * cp.quad_form(x, cp.psd_wrap(S)) - c)), cons).solve(**SOLV)
    return x.value, (float(b.dual_value) / BP if budget else None)


def joint(I):
    x0 = cp.Variable(n); u0 = cp.Variable(n, nonneg=True); d0 = cp.Variable(n, nonneg=True); c0 = I['kp'] @ u0 + I['km'] @ d0; h0 = I['h'] - cp.sum(x0 - I['x0']) - c0
    cons = [x0 - I['x0'] == u0 - d0] + box(x0, I); b0 = h0 >= 0; cons.append(b0); mu0, S0 = I['m0']
    obj = mu0 @ x0 - GAM / 2 * cp.quad_form(x0, cp.psd_wrap(S0)) - c0; X1, bs, mk = [], [], []
    for z in I['Z']:
        x1 = cp.Variable(n); u = cp.Variable(n, nonneg=True); d = cp.Variable(n, nonneg=True); c1 = I['kp'] @ u + I['km'] @ d
        m = x1 - cp.multiply(z['g'], x0) == u - d; cons += [m] + box(x1, I); mk.append(m)
        bb = h0 - cp.sum(x1 - cp.multiply(z['g'], x0)) - c1 >= 0; cons.append(bb); bs.append(bb); X1.append(x1)
        obj = obj + BETA * z['q'] * (z['m'][0] @ x1 - GAM / 2 * cp.quad_form(x1, cp.psd_wrap(z['m'][1])) - c1)
    cp.Problem(cp.Maximize(BP * obj), cons).solve(**SOLV)
    e0 = float(b0.dual_value) / BP; e1 = [float(bb.dual_value) / BP / (BETA * z['q']) for bb, z in zip(bs, I['Z'])]
    # incumbent values from the marking duals (cvxpy's sign convention, checked against tomorrow's regimes): S = sum_z g(z) nu(z) + beta E[g eta_1]
    Sd = sum(z['g'] * np.asarray(m.dual_value) for z, m in zip(I['Z'], mk)) / BP + BETA * sum(z['q'] * z['g'] * e for z, e in zip(I['Z'], e1))
    return x0.value, [x.value for x in X1], e0, e1, Sd


def svals(I, x0, X1, e1):
    S = np.zeros(n)
    for z, x1, e in zip(I['Z'], X1, e1):
        xm = z['g'] * x0; g1 = z['m'][0] - GAM * z['m'][1] @ x1
        for i in range(n):
            d = x1[i] - xm[i]
            if d > 1e-7: s = e + (1 + e) * I['kp'][i]
            elif d < -1e-7: s = e - (1 + e) * I['km'][i]
            elif 1e-7 < x1[i] < I['cap'][i] - 1e-7: s = g1[i]
            else: return None
            S[i] += BETA * z['q'] * z['g'][i] * s
    return S


def liq_need(I, x0, h, z):
    mu, S = z['m']; xh = np.maximum(mu - I['kp'], 0) / (GAM * np.diag(S)); xs = (mu[2] + I['km'][2]) / (GAM * S[2, 2])
    parts = [(1 + I['kp'][i]) * max(xh[i] - z['g'][i] * x0[i], 0) for i in range(n)]
    return h + (1 - I['km'][2]) * max(z['g'][2] * x0[2] - max(xs, 0), 0), sum(parts), parts


def clip_err(I, x0, S, eh):
    mu0, S0 = I['m0']; r = I['b'][:NF] / I['b'][2]; m = mu0[2] - GAM * I['sEE'] * (x0[2] + r @ x0[:NF]); at = mu0[:NF] - r * mu0[2]; err = []
    for i in range(NF):
        lo = (at[i] + S[i] + r[i] * m - eh - (1 + eh) * I['kp'][i]) / (GAM * I['v'][i]); hi = (at[i] + S[i] + r[i] * m - eh + (1 + eh) * I['km'][i]) / (GAM * I['v'][i])
        err.append(abs(np.clip(np.clip(I['x0'][i], lo, hi), 0, I['cap'][i]) - x0[i]))
    return err, m


def cell(args):
    I = build(*args); mu0, S0 = I['m0']; rng = np.random.default_rng([555, hash(args) % 100000])
    x0, X1, e0, e1, Sd = joint(I); eh = e0 + BETA * np.mean(e1); h0 = I['h'] - spend(x0, I['x0'], I)
    Sr = svals(I, x0, X1, e1); dual_vs_regime = None if Sr is None else np.abs(Sd - Sr).max()
    err, m = clip_err(I, x0, Sd, eh)
    xm0, em0 = review(mu0, S0, I['x0'], I['h'], I); hm = I['h'] - spend(xm0, I['x0'], I)
    # 2(a)
    roots = [(x0, max(h0, 0))] + [(xm0, max(hm, 0))] + [(np.array([rng.uniform(0, 0.25), rng.uniform(0, 0.25), rng.uniform(0, 1)]), rng.uniform(0, 0.1)) for _ in range(10)]
    cov = via = fail = 0
    for xr, hr in roots:
        for z in I['Z']:
            liq, need, _ = liq_need(I, xr, hr, z)
            if liq >= need:
                cov += 1; via += hr < need
                xu, _ = review(*z['m'], z['g'] * xr, hr, I, budget=False); fail += spend(xu, z['g'] * xr, I) - hr > 1e-9
    # 2(b)
    allcov = all(liq_need(I, x0, h0, z)[0] >= liq_need(I, x0, h0, z)[1] for z in I['Z'])
    p2b = None
    if allcov and h0 > 1e-6:
        br = all(-BETA * np.mean([z['g'][i] for z in I['Z']]) * I['km'][i] - 1e-9 <= Sd[i] <= BETA * np.mean([z['g'][i] for z in I['Z']]) * I['kp'][i] + 1e-9 for i in range(n))
        p2b = (max(e1) < 1e-8) and br
    # 2(c)
    p2c = []
    for xr, hr in ((x0, h0), (xm0, hm)):
        P = np.array([liq_need(I, xr, hr, z)[2] for z in I['Z']]); tot = P.sum(1); lhs, rhs = tot.max(), P.max(0).sum()
        common = any(np.all(P[k] >= P.max(0) - 1e-12) for k in range(len(P)))
        p2c.append((lhs <= rhs + 1e-12, (abs(lhs - rhs) <= 1e-12) == common))
    # 3(b)
    Sm = np.zeros(n); r = I['b'][:NF] / I['b'][2]; mm = mu0[2] - GAM * I['sEE'] * (xm0[2] + r @ xm0[:NF]); p3 = []
    for i in range(NF):
        dd, dm = x0[i] - I['x0'][i], xm0[i] - I['x0'][i]
        if ((dd > 1e-6 and dm > 1e-6) or (dd < -1e-6 and dm < -1e-6)) and all(1e-6 < x[i] < 0.25 - 1e-6 for x in (x0, xm0)):
            k = I['kp'][i] if dd > 0 else -I['km'][i]
            p3.append(abs((Sd[i] + r[i] * (m - mm) - (eh - em0) * (1 + k)) / (GAM * I['v'][i]) - (x0[i] - xm0[i])))
    # part 4
    Rv = (x0[2] + h0) - (xm0[2] + hm); C = lambda x: I['kp'] @ np.maximum(x - I['x0'], 0) + I['km'] @ np.maximum(I['x0'] - x, 0)
    ident = abs(Rv - ((xm0[:NF] - x0[:NF]).sum() + C(xm0) - C(x0)))
    bound = sum((abs(Sd[i]) + abs(r[i]) * abs(m - mm) + abs(eh - em0) * (1 + I['kp'][i])) / (GAM * I['v'][i]) for i in range(NF)) + abs(C(xm0) - C(x0))
    return dict(cell=args, err=err, dvr=dual_vs_regime, cov=cov, via=via, fail=fail, nroots=len(roots), p2b=p2b, p2c=p2c, p3=p3, ident=ident, bound_ok=abs(Rv) <= bound + 1e-9,
                eta_pos=max(e1) > 1e-8)


if __name__ == "__main__":
    grid = list(itertools.product(PRE, STARTS.values(), [0.30, 0.02], ["preset", "rev x4", "ETF sale x3"]))
    with Pool(9) as p: O = p.map(cell, grid)
    E = [e for o in O for e in o['err']]; D = [o['dvr'] for o in O if o['dvr'] is not None]
    print(f"48 cells. 1(b): {len(E)} fund-cells, largest clip error {max(E):.2e} (above 1e-6: {sum(e > 1e-6 for e in E)}); marking-dual S vs regime S where pinned: {len(D)} cells, max {max(D):.1e}")
    print(f"2(a): {sum(o['nroots'] for o in O)} roots, {sum(o['nroots'] for o in O) * 64} states: covered {sum(o['cov'] for o in O)}, only through the ETF's proceeds {sum(o['via'] for o in O)}, failures {sum(o['fail'] for o in O)}")
    B = [o['p2b'] for o in O if o['p2b'] is not None]; print(f"2(b): {len(B)} cells with every state covered and h > 0; all hold: {sum(B)}")
    print(f"2(c): bound at both roots {sum(all(a for a, _ in o['p2c']) for o in O)}/48; equality iff a common worst state {sum(all(c for _, c in o['p2c']) for o in O)}/48")
    P3 = [e for o in O for e in o['p3']]; print(f"3(b): {len(P3)} fund-cells in the domain, largest error {max(P3):.1e}")
    print(f"part 4: identity max {max(o['ident'] for o in O):.1e}; |R| bound {sum(o['bound_ok'] for o in O)}/48; cells with a positive cash price tomorrow {sum(o['eta_pos'] for o in O)}")
