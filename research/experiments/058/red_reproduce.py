"""Red's reproduction of experiment 058 (D26's integrated example), written from the registration without reading run.py, report.py,
harness_n or experiments/d26-prep. M9 with two factors, three funds, two ETFs (fees and tracking residuals), cash; the axis law (2d atoms
at +- sqrt(d) sd per block: 10 parameter atoms x 14 shock atoms = 140 states); red's own cvxpy/CLARABEL programs. Per case: the three
policies' values and V^dyn (losses in bp of W_0), claim 049's band term at x^my_0 and claim 115's at x^my_0 and x^s_0 (each minimized over
the admissible incumbent-value box at the relaxed tomorrow), the tail term and coverage at both roots.
Run: uv run python experiments/058/red_reproduce.py [worked | sample]"""
import sys, itertools, numpy as np, cvxpy as cp, warnings
from multiprocessing import Pool
warnings.simplefilter('ignore'); GAM, BETA, BP = 5.0, 1.0, 1e4
SOLV = dict(solver=cp.CLARABEL, tol_gap_abs=1e-12, tol_gap_rel=1e-12, tol_feas=1e-12, max_iter=1000)
PRE = {"equity-style": dict(alpha=-0.0019, fund=0.0050, etf=0.0002), "fixed-income-style": dict(alpha=0.0020, fund=0.0020, etf=0.0050)}
BA = np.array([[1.0, 0.2], [0.8, 0.6], [0.5, 1.0]]); BE = np.array([[1.0, 0.0], [0.3, 1.0]]); NF, M, K = 3, 2, 2; n = NF + M
SA = np.array([0.02, 0.025, 0.03]); SE = np.array([0.002, 0.003]); CE = np.array([0.0003, 0.0005]); SF = np.array([0.08, 0.04])
LAM, SL, ASD = np.array([0.015, 0.005]), np.array([0.005, 0.005]), 0.0035
STARTS = {"cash": (np.zeros(5), 1.0), "rebal": (np.array([0.10, 0.10, 0.05, 0.40, 0.20]), 0.15), "tight": (np.array([0.10, 0.10, 0.05, 0.40, 0.20]), 0.02)}


def build(regime, start, setting, BAx=BA):
    P = PRE[regime]; B = np.vstack([BAx, BE]); am = P['alpha'] + np.array([0.0, 0.002, -0.001]); pa = np.full(3, ASD ** 2); pl = SL ** 2
    phi = np.ones(5); tb = np.concatenate([LAM, am]); q = np.zeros(5)
    kp = np.concatenate([P['fund'] * np.array([1, 1.5, 0.75]), P['etf'] * np.array([1, 1.5])])
    if setting.startswith('pred_alpha'):
        d = float(setting.split()[1]); phi[2:] = 0.5; tb[2:] = am + d
        if 'unc' in setting: pa = pa * 4
    if setting.startswith('pred_lambda'): d = float(setting.split()[1]); phi[:2] = 0.7; tb[0] = LAM[0] + d   # M9's Phi is per block: phi_lambda on both premia
    if setting == 'unc x0.25': pa = pa * 0.25
    if setting == 'unc x4': pa = pa * 4
    if setting == 'q_alpha 1e-6': q[2:] = 1e-6
    if setting == 'fund rates x2': kp[:3] *= 2
    if setting == 'ETF rates x4': kp[3:] *= 4
    if setting == 'ETF rates x0.25': kp[3:] *= 0.25
    x0, h = STARTS[start]
    def mom(m, p):
        Sf = np.diag(SF ** 2 + p[:2]); mu = np.concatenate([m[2:] + BAx @ m[:2], BE @ m[:2] - CE])
        return mu, B @ Sf @ B.T + np.diag(np.concatenate([SA ** 2 + p[2:], SE ** 2]))
    m0 = np.concatenate([LAM, am]); p0 = np.concatenate([pl, pa]); R = np.concatenate([SF ** 2, SA ** 2]); Kg = p0 / (p0 + R)
    pu = (1 - Kg) * p0; p1 = phi ** 2 * pu + q
    I = dict(kp=kp, km=kp.copy(), cap=np.array([0.25, 0.25, 0.25, np.inf, np.inf]), x0=x0.astype(float), h=h, m0=mom(m0, p0), Z=[], W0=h + x0.sum())
    S1 = mom(m0, p1)[1]; sd_p = np.sqrt(p0); sd_s = np.concatenate([SF, SA, SE])
    for kp_, sp in itertools.product(range(10), range(14)):
        th = m0.copy(); th[kp_ // 2] += (1 if kp_ % 2 == 0 else -1) * np.sqrt(5) * sd_p[kp_ // 2]
        z = np.zeros(7); z[sp // 2] = (1 if sp % 2 == 0 else -1) * np.sqrt(7) * sd_s[sp // 2]
        f = th[:2] + z[:2]; rA = BAx @ f + th[2:] + z[2:5]; rE = BE @ f - CE + z[5:7]
        y = np.concatenate([f, th[2:] + z[2:5]]); mu_ = m0 + Kg * (y - m0); m1 = phi * mu_ + (1 - phi) * tb
        I['Z'].append(dict(q=1 / 140, g=1 + np.concatenate([rA, rE]), m=(mom(m1, p1)[0], S1)))
    assert min(z['g'].min() for z in I['Z']) > 0
    return I


def spend(x, xm, I): d = x - xm; return d.sum() + I['kp'] @ np.maximum(d, 0) + I['km'] @ np.maximum(-d, 0)
def cost(x, xm, I): d = x - xm; return I['kp'] @ np.maximum(d, 0) + I['km'] @ np.maximum(-d, 0)
def score(mu, S, x, xm, I): return mu @ x - GAM / 2 * x @ S @ x - cost(x, xm, I)
def box(x, I): return [x >= 0, x[:NF] <= I['cap'][:NF]]


def review(mu, S, xm, h, I, budget=True):
    x = cp.Variable(n); u = cp.Variable(n, nonneg=True); d = cp.Variable(n, nonneg=True); c = I['kp'] @ u + I['km'] @ d
    cons = [x - xm == u - d] + box(x, I)
    if budget: cons.append(h - cp.sum(x - xm) - c >= 0)
    cp.Problem(cp.Maximize(BP * (mu @ x - GAM / 2 * cp.quad_form(x, cp.psd_wrap(S)) - c)), cons).solve(**SOLV); return x.value


def joint(I, tomorrow_budget=True):
    x0 = cp.Variable(n); u0 = cp.Variable(n, nonneg=True); d0 = cp.Variable(n, nonneg=True); c0 = I['kp'] @ u0 + I['km'] @ d0; h0 = I['h'] - cp.sum(x0 - I['x0']) - c0
    cons = [x0 - I['x0'] == u0 - d0, h0 >= 0] + box(x0, I); mu0, S0 = I['m0']; obj = mu0 @ x0 - GAM / 2 * cp.quad_form(x0, cp.psd_wrap(S0)) - c0
    for z in I['Z']:
        x1 = cp.Variable(n); u = cp.Variable(n, nonneg=True); d = cp.Variable(n, nonneg=True); c1 = I['kp'] @ u + I['km'] @ d
        cons += [x1 - cp.multiply(z['g'], x0) == u - d] + box(x1, I)
        if tomorrow_budget: cons.append(h0 - cp.sum(x1 - cp.multiply(z['g'], x0)) - c1 >= 0)
        obj = obj + BETA * z['q'] * (z['m'][0] @ x1 - GAM / 2 * cp.quad_form(x1, cp.psd_wrap(z['m'][1])) - c1)
    pr = cp.Problem(cp.Maximize(BP * obj), cons); pr.solve(**SOLV); return x0.value, pr.value / BP


def J(I, x0):
    """today's score net of costs plus beta E[tomorrow's funded one-review optimum]; also E tomorrow's cost and the relaxed tomorrow."""
    mu0, S0 = I['m0']; h = max(I['h'] - spend(x0, I['x0'], I), 0.0); v = score(mu0, S0, x0, I['x0'], I); c1 = 0.0; rel = []
    for z in I['Z']:
        xm = z['g'] * x0; x1 = review(*z['m'], xm, h, I); v += BETA * z['q'] * score(*z['m'], x1, xm, I); c1 += z['q'] * cost(x1, xm, I)
        rel.append(review(*z['m'], xm, h, I, budget=False))
    return v, c1, rel, h


def bound_terms(I, x0, rel, h):
    """claim 049's band (min over the admissible box) and claim 115's rho form at x0; the tail term and coverage."""
    mu0, S0 = I['m0']; A = np.linalg.inv(GAM * S0); g0 = mu0 - GAM * S0 @ x0; cons = []; Sx = [0] * n; tail = 0.0; unc = 0; needs = []
    for z, xu in zip(I['Z'], rel):
        xm = z['g'] * x0; g1 = z['m'][0] - GAM * z['m'][1] @ xu
        for i in range(n):
            d = xu[i] - xm[i]
            if d > 1e-7: t = I['kp'][i]
            elif d < -1e-7: t = -I['km'][i]
            elif 1e-7 < xu[i] < I['cap'][i] - 1e-7: t = g1[i]
            else:
                t = cp.Variable(); gc = min(max(g1[i], -I['km'][i]), I['kp'][i])           # the held marginal, clipped into the band (solver noise)
                cons += [t >= (gc if xu[i] <= 1e-7 else -I['km'][i]), t <= (I['kp'][i] if xu[i] <= 1e-7 else gc)]
            Sx[i] = Sx[i] + BETA * z['q'] * z['g'][i] * t
        mu, S = z['m']; xh = np.maximum(mu - I['kp'], 0) / (GAM * np.diag(S)); need = sum((1 + I['kp'][i]) * max(xh[i] - xm[i], 0) for i in range(n))
        xc = (mu[NF:] + I['km'][NF:]) / (GAM * np.diag(S)[NF:]); liq = h + sum((1 - I['km'][NF + j]) * max(xm[NF + j] - max(xc[j], 0), 0) for j in range(M))
        eb = max(max(mu[i] - I['kp'][i], 0) / (1 + I['kp'][i]) for i in range(n)); D = max(need - liq, 0); tail += BETA * z['q'] * eb * D; unc += D > 0; needs.append(need)
    Svec = cp.hstack([s if isinstance(s, cp.Expression) else cp.Constant(s) for s in Sx])
    p049 = cp.Problem(cp.Minimize(0.5 * cp.quad_form(Svec, cp.psd_wrap(A))), cons); qsolve(p049)
    eta = cp.Variable(nonneg=True); sg = cp.Variable(n); nn = cp.Variable(n); c2 = list(cons) + [eta <= 1]
    if h > 1e-9: c2.append(eta == 0)
    for i in range(n):
        d = x0[i] - I['x0'][i]
        if d > 1e-9: c2.append(sg[i] == (1 + eta) * I['kp'][i])
        elif d < -1e-9: c2.append(sg[i] == -(1 + eta) * I['km'][i])
        else: c2 += [sg[i] <= (1 + eta) * I['kp'][i], sg[i] >= -(1 + eta) * I['km'][i]]
        atz = x0[i] <= 1e-9; atc = x0[i] >= I['cap'][i] - 1e-9
        c2.append(nn[i] <= 0 if atz else (nn[i] >= 0 if atc else nn[i] == 0))
    r = g0 + Svec - eta - sg - nn
    p115 = cp.Problem(cp.Minimize(0.5 * cp.quad_form(r, cp.psd_wrap(A))), c2); qsolve(p115)
    W = I['W0']; return dict(b049=p049.value * 1e4 / W, b115=p115.value * 1e4 / W, tail=tail * 1e4 / W, eps=unc / len(I['Z']), need=(min(needs), max(needs)))


def qsolve(pr):
    for kw in (dict(solver=cp.CLARABEL), dict(solver=cp.SCS, eps=1e-11, max_iters=500000), dict()):
        try:
            pr.solve(**kw)
            if pr.status in ('optimal', 'optimal_inaccurate'): return
        except cp.error.SolverError: pass
    raise RuntimeError('band QP unsolved')


def case(args):
    regime, start, setting = args; I = build(regime, start, setting); mu0, S0 = I['m0']
    xd, Vd = joint(I); xs, _ = joint(I, tomorrow_budget=False); xm = review(mu0, S0, I['x0'], I['h'], I)
    Jm, c1m, relm, hm = J(I, xm); Js, c1s, rels, hs = J(I, xs)
    bm = bound_terms(I, xm, relm, hm); bs = bound_terms(I, xs, rels, hs)
    W = I['W0']                                                                                         # bp of initial wealth W_0 = h^- + sum x^- (holdings at par)
    return dict(case=args, loss1=(Vd - Jm) * 1e4 / W, loss2=(Vd - Js) * 1e4 / W, xm=xm, xs=xs, xd=xd, hm=hm, hs=hs, cost0m=cost(xm, I['x0'], I) * 1e4 / W, cost0s=cost(xs, I['x0'], I) * 1e4 / W,
                cost1m=c1m * 1e4 / W, cost1s=c1s * 1e4 / W, bm=bm, bs=bs)


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else 'worked'
    if mode == 'worked':
        o = case(("fixed-income-style", "rebal", "pred_alpha 0.004"))
        for name, x, h, c0, c1, L in (("1 one-review", o['xm'], o['hm'], o['cost0m'], o['cost1m'], o['loss1']), ("2 plan w/o tomorrow's budget", o['xs'], o['hs'], o['cost0s'], o['cost1s'], o['loss2'])):
            print(f"{name}: holdings {x.round(3)} cash {h:.3f}; today's cost {c0:.1f} bp, E tomorrow's cost {c1:.1f} bp; loss {L:.3f} bp")
        print(f"3 dynamic: {o['xd'].round(3)}")
        print(f"bounds at x^my: claim 049 band {o['bm']['b049']:.0f} bp, claim 115 band {o['bm']['b115']:.0f} bp, tail {o['bm']['tail']:.0f} bp, eps {o['bm']['eps']:.2f}, need {o['bm']['need'][0]:.2f}-{o['bm']['need'][1]:.2f}")
        print(f"bounds at x^s: claim 115 band {o['bs']['b115']:.2e} bp, tail {o['bs']['tail']:.0f} bp, eps {o['bs']['eps']:.2f}")
    else:
        settings = ["base", "pred_alpha 0.004", "pred_alpha -0.004", "pred_lambda 0.005", "pred_lambda -0.005", "unc x0.25", "unc x4", "pred_alpha 0.004 unc", "pred_alpha 0.008",
                    "q_alpha 1e-6", "fund rates x2", "ETF rates x4", "ETF rates x0.25"]
        grid = [(r, s, st) for r in PRE for s in ("rebal", "cash", "tight") for st in settings]
        with Pool(8) as p: O = p.map(case, grid)
        import json
        json.dump([dict(case=o['case'], loss1=o['loss1'], loss2=o['loss2'], b115m=o['bm']['b115'], b049m=o['bm']['b049'], tailm=o['bm']['tail'], tails=o['bs']['tail']) for o in O],
                  open(sys.argv[2] if len(sys.argv) > 2 else '/dev/null', 'w'))
        print(f"{len(O)} cases: policy 2's loss max {max(o['loss2'] for o in O):.4f} bp; one-review loss {min(o['loss1'] for o in O):.2f}-{max(o['loss1'] for o in O):.2f} bp")
        print(f"coverage fails at eps = 0 at both roots in {sum(o['bm']['eps'] > 0 and o['bs']['eps'] > 0 for o in O)} of {len(O)}; eps = 1 at x^my in {sum(o['bm']['eps'] == 1 for o in O)}")
        print(f"claim 115 band at x^my >= one-review loss in {sum(o['bm']['b115'] >= o['loss1'] - 1e-6 for o in O)} of {len(O)} (loss/band median {np.median([o['loss1'] / o['bm']['b115'] for o in O if o['bm']['b115'] > 0]):.2f}, max {max(o['loss1'] / o['bm']['b115'] for o in O if o['bm']['b115'] > 0):.2f})")
        print(f"claim 115 band at x^s max {max(o['bs']['b115'] for o in O):.1e} bp; tail at x^my {min(o['bm']['tail'] for o in O):.0f}-{max(o['bm']['tail'] for o in O):.0f} bp")
        for r in PRE:
            for s in ("cash", "rebal"):
                L = [o['loss1'] for o in O if o['case'][0] == r and o['case'][1] == s]; print(f"  {r} {s}: one-review loss {min(L):.2f}-{max(L):.2f} bp")
