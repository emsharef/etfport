"""Red's reproduction of experiment 057 (claim 114 on M9), written from the registered Design without reading experiments/057/run.py or
harness_n's M9 path. One fund and one ETF (b_A = b_E = 1, no ETF residual), the presets; the tree is M8's at t = 0 (returns over (0, 1]
carry theta_0), with tomorrow's moments from M9's predict step m_1 = Phi (m_0 + K nu) + (I - Phi) theta_bar, P_1 = Phi P^u Phi + Q.
Checks: 1a (decomposition, E and Cov of Delta^u), 1b (the per-instrument width iff over 10 steps, psd cases, monotone blocks, the named
instances at the preset and at the worked-example inputs), part 2 (the up-down identity), 3a-3b (the 108 cells, the ETF frozen).
Run: uv run python experiments/057/red_reproduce.py"""
import itertools, numpy as np, cvxpy as cp, warnings
from multiprocessing import Pool
warnings.simplefilter('ignore'); GAM, BETA, BP = 5.0, 1.0, 1e4
SOLV = dict(solver=cp.CLARABEL, tol_gap_abs=1e-12, tol_gap_rel=1e-12, tol_feas=1e-12, max_iter=500)
PRE = {"equity-style": dict(alpha=-0.0019, fund=0.0050, etf=0.0002), "fixed-income-style": dict(alpha=0.0020, fund=0.0020, etf=0.0050)}


def model(regime=None, phi=(1.0, 1.0), q=(0.0, 0.0), dalpha=0.0, bA=1.0, sf=0.08, sA=0.02, P0=None, lam=0.015, alpha=None):
    P = PRE[regime] if regime else dict(alpha=0.004, fund=0.005, etf=0.001)
    M = dict(bA=bA, bE=1.0, sf=sf, sA=sA, Phi=np.array(phi), Q=np.array(q), m0=np.array([lam, P['alpha'] if alpha is None else alpha]),
             P0=np.array([0.005 ** 2, 0.0035 ** 2]) if P0 is None else np.array(P0), kp=np.array([P['fund'], P['etf']]), cap=0.25)
    M['km'] = M['kp'].copy(); M['tb'] = M['m0'] + np.array([0.0, dalpha]); M['R'] = np.array([sf ** 2, sA ** 2])
    M['G'] = np.array([[bA, 1.0], [1.0, 0.0]]); M['Sr'] = np.array([[bA ** 2 * sf ** 2 + sA ** 2, bA * sf ** 2], [bA * sf ** 2, sf ** 2]])
    return M


def Sig(M, p): return M['G'] @ np.diag(p) @ M['G'].T + M['Sr']
def mu(M, m): return M['G'] @ m


def step(M, p):
    pu = p - p ** 2 / (p + M['R']); return M['Phi'] ** 2 * pu + M['Q'], pu


def tree(M):
    """review-1 nodes: q, marking g, filtered-and-predicted mean m_1, innovation nu."""
    p0 = M['P0']; K = p0 / (p0 + M['R']); p1, pu = step(M, p0); Z = []
    for sg in itertools.product([-1, 1], repeat=4):
        th = M['m0'] + np.array(sg[:2]) * np.sqrt(p0); z = np.array(sg[2:]) * np.sqrt(M['R'])
        y = th + z; nu = y - M['m0']; m1 = M['Phi'] * (M['m0'] + K * nu) + (1 - M['Phi']) * M['tb']
        f = y[0]; g = np.array([1 + M['bA'] * f + y[1] - M['bA'] * f + M['bA'] * f, 1 + f])   # r_A = b_A f + alpha + z_A; y[1] = alpha + z_A
        g[0] = 1 + M['bA'] * f + y[1]
        Z.append(dict(q=1 / 16, g=g, m1=m1, nu=nu))
    return Z, p1, pu, K


def check1(M):
    Z, p1, pu, K = tree(M); S0, S1 = Sig(M, M['P0']), Sig(M, p1); mu0 = mu(M, M['m0']); A0, A1 = np.linalg.inv(GAM * S0), np.linalg.inv(GAM * S1)
    Dp = A1 @ M['G'] @ ((M['Phi'] - 1) * (M['m0'] - M['tb'])) + (A1 - A0) @ mu0
    Du = np.array([A1 @ M['G'] @ (M['Phi'] * K * z['nu']) for z in Z]); dec = max(np.abs(A1 @ mu(M, z['m1']) - A0 @ mu0 - (Dp + d)).max() for z, d in zip(Z, Du))
    V0 = np.diag(M['Phi'] ** 2 * (M['P0'] - pu)); cov = (Du.T @ Du) / 16; covf = A1 @ M['G'] @ V0 @ M['G'].T @ A1
    # part 2's identity, per instrument, on the tree's law of Delta^u
    p2 = []
    for i in range(2):
        v = Du[:, i]; dp = Dp[i]; sym = np.allclose(np.sort(v), np.sort(-v), atol=1e-13)
        U, D = np.mean(v > -dp), np.mean(v < -dp); half = np.mean((v > -abs(dp)) & (v <= abs(dp)))
        p2.append((sym, abs((U - D) - np.sign(dp) * half) if sym else None))
    return dec, np.abs(Du.mean(0)).max(), np.abs(cov - covf).max() / np.abs(covf).max(), p2


def check1b(M, T=10):
    """per-instrument width iff over T steps; psd cases; monotone blocks."""
    p = M['P0'].copy(); iff = knife = below = above = below_ok = above_ok = 0; ps = [p.copy()]
    for _ in range(T):
        pn, pu = step(M, p); dP = pn - p; w = lambda pp: (M['kp'] + M['km']) / (GAM * np.diag(Sig(M, pp)))
        crit = np.diag(M['G'] @ np.diag(dP) @ M['G'].T); rises = w(pn) > w(p)
        for i in range(2):
            if abs(crit[i]) < 1e-14: knife += 1
            else: iff += rises[i] == (crit[i] < 0)
        if (dP <= 0).all(): below += 1; below_ok += rises.all()
        if (dP >= 0).all() and (dP > 0).any(): above += 1; above_ok += (~rises).all()
        p = pn; ps.append(p.copy())
    ps = np.array(ps); mono = all((np.diff(ps[:, k]) >= -1e-18).all() or (np.diff(ps[:, k]) <= 1e-18).all() for k in range(2))
    return iff, knife, below, below_ok, above, above_ok, mono


def pattern(M):
    """one step at t = 0: fund width change sign, ETF width change sign, psd relations."""
    p1, _ = step(M, M['P0']); dP = p1 - M['P0']; w = lambda pp: (M['kp'] + M['km']) / (GAM * np.diag(Sig(M, pp)))
    return dict(fund_rises=w(p1)[0] > w(M['P0'])[0], etf_rises=w(p1)[1] > w(M['P0'])[1], psd_below=(dP <= 0).all(), psd_above=(dP >= 0).all(), dP=dP)


def review_frozenE(mu_, S, xm, h, M):
    """one-review problem with the ETF frozen at its incumbent."""
    x = cp.Variable(2); u = cp.Variable(nonneg=True); d = cp.Variable(nonneg=True); c = M['kp'][0] * u + M['km'][0] * d
    b = h - (x[0] - xm[0]) - c >= 0
    cp.Problem(cp.Maximize(BP * (mu_ @ x - GAM / 2 * cp.quad_form(x, cp.psd_wrap(S)) - c)), [x[0] - xm[0] == u - d, x[1] == xm[1], x[0] >= 0, x[0] <= M['cap'], b]).solve(**SOLV)
    return x.value, float(b.dual_value) / BP


def joint_frozenE(M, Z, p1, x0m, h):
    S0 = Sig(M, M['P0']); S1 = Sig(M, p1); mu0 = mu(M, M['m0'])
    x0 = cp.Variable(2); u0 = cp.Variable(nonneg=True); d0 = cp.Variable(nonneg=True); c0 = M['kp'][0] * u0 + M['km'][0] * d0; h0 = h - (x0[0] - x0m[0]) - c0
    b0 = h0 >= 0; cons = [x0[0] - x0m[0] == u0 - d0, x0[1] == x0m[1], x0[0] >= 0, x0[0] <= M['cap'], b0]
    obj = mu0 @ x0 - GAM / 2 * cp.quad_form(x0, cp.psd_wrap(S0)) - c0; X1, bs = [], []
    for z in Z:
        x1 = cp.Variable(2); u = cp.Variable(nonneg=True); d = cp.Variable(nonneg=True); c1 = M['kp'][0] * u + M['km'][0] * d
        cons += [x1[0] - z['g'][0] * x0[0] == u - d, x1[1] == z['g'][1] * x0[1], x1[0] >= 0, x1[0] <= M['cap']]
        bb = h0 - (x1[0] - z['g'][0] * x0[0]) - c1 >= 0; cons.append(bb); bs.append(bb); X1.append(x1)
        obj = obj + BETA * z['q'] * (mu(M, z['m1']) @ x1 - GAM / 2 * cp.quad_form(x1, cp.psd_wrap(S1)) - c1)
    cp.Problem(cp.Maximize(BP * obj), cons).solve(**SOLV)
    return x0.value, [x.value for x in X1], float(b0.dual_value) / BP, [float(bb.dual_value) / BP / (BETA * z['q']) for bb, z in zip(bs, Z)]


def cell3(args):
    kw, a0 = args; M = model(**kw); Z, p1, pu, K = tree(M); S0 = Sig(M, M['P0']); S1 = Sig(M, p1); mu0 = mu(M, M['m0']); x0m = np.array([a0, 0.4]); h = 1.0
    xm0, em0 = review_frozenE(mu0, S0, x0m, h, M); hm = h - (xm0[0] - a0) - M['kp'][0] * max(xm0[0] - a0, 0) - M['km'][0] * max(a0 - xm0[0], 0)
    T1 = [review_frozenE(mu(M, z['m1']), S1, z['g'] * xm0, hm, M)[0] for z in Z]; tr = [x[0] - z['g'][0] * xm0[0] for z, x in zip(Z, T1)]
    kind = '3a' if all(t > 1e-7 for t in tr) else ('3b' if all(t < -1e-7 for t in tr) else None)
    if kind is None: return None
    x0, X1, e0, e1 = joint_frozenE(M, Z, p1, x0m, h); hd = h - (x0[0] - a0) - M['kp'][0] * max(x0[0] - a0, 0) - M['km'][0] * max(a0 - x0[0], 0)
    slack = hm > 1e-6 and hd > 1e-6 and max(e1) < 1e-8 and em0 < 1e-8 and e0 < 1e-8
    if not slack: return dict(kind=kind, hyp=False)
    Eg = np.mean([z['g'][0] for z in Z]); k = M['kp'][0] if kind == '3a' else -M['km'][0]
    Smy = BETA * np.mean([z['g'][0] * (M['kp'][0] if kind == '3a' else -M['km'][0]) for z in Z])
    trd = [x[0] - z['g'][0] * x0[0] for z, x in zip(Z, X1)]; ntr = sum((t > 1e-7) if kind == '3a' else (t < -1e-7) for t in trd)
    Sd = 0.0
    for z, x1, t in zip(Z, X1, trd):
        g1 = (mu(M, z['m1']) - GAM * S1 @ x1)[0]
        s = M['kp'][0] if t > 1e-7 else (-M['km'][0] if t < -1e-7 else (g1 if 1e-7 < x1[0] < M['cap'] - 1e-7 else np.nan))
        Sd += BETA * z['q'] * z['g'][0] * s
    g0 = (mu0 - GAM * S0 @ x0)[0]; traded = abs(x0[0] - a0) > 1e-7
    return dict(kind=kind, hyp=True, pinned=abs(Smy - BETA * Eg * k) if True else None, order=(x0[0] >= xm0[0] - 1e-7) if kind == '3a' else (x0[0] <= xm0[0] + 1e-7),
                ntr=ntr, Sd_inside=abs(Sd) < BETA * Eg * abs(k) - 1e-9 if not np.isnan(Sd) else None, traded=traded, g0=g0 if traded else None, claimed=(1 - BETA * Eg) * k,
                rootline=abs(g0 + Sd - k) if traded and not np.isnan(Sd) else None, regime=kw['regime'])


if __name__ == "__main__":
    grid = [dict(regime=r, phi=ph, q=qq, dalpha=da) for r in PRE for ph in [(1.0, 0.5), (0.9, 0.5), (0.7, 0.9)] for qq in [(0, 0), (1e-6, 1e-7), (0, 1e-6)] for da in (0.006, -0.006)]
    R1 = [check1(model(**kw)) for kw in grid]
    print(f"1a (36 models): decomposition {max(r[0] for r in R1):.1e}; E Delta^u {max(r[1] for r in R1):.1e}; covariance relative error {max(r[2] for r in R1):.1e}")
    P2 = [x for r in R1 for x in r[3]]; print(f"part 2: {len(P2)} instrument-models, symmetric {sum(x[0] for x in P2)}; identity error {max((x[1] for x in P2 if x[1] is not None), default=0):.1e}")
    B = [check1b(model(**kw)) for kw in grid]
    print(f"1b (36 models, 10 steps): per-instrument iff {sum(b[0] for b in B)}/{720 - sum(b[1] for b in B)} (knife edges {sum(b[1] for b in B)}); psd-below steps {sum(b[2] for b in B)}, every width rising {sum(b[3] for b in B)}; "
          f"psd-above steps {sum(b[4] for b in B)}, every width falling {sum(b[5] for b in B)}; blocks monotone {sum(b[6] for b in B)}/36")
    wk = dict(bA=0.9, sf=0.0801, sA=0.0632, P0=(1.6e-5, 4e-4), lam=0.01, alpha=0.004)
    for name, M in (("red's, preset", model('equity-style', phi=(1, 1), q=(0, 1e-4))), ("lean's, preset", model('equity-style', phi=(1, 1), q=(1e-6, 0), bA=0.9)),
                    ("red's, worked example", model(phi=(1, 1), q=(0, 1e-4), **wk)), ("lean's (q_lambda = 1e-5), worked example", model(phi=(1, 1), q=(1e-5, 0), **wk))):
        pt = pattern(M); print(f"  {name}: fund width {'rises' if pt['fund_rises'] else 'falls'}, ETF width {'rises' if pt['etf_rises'] else 'falls'}; psd below {pt['psd_below']}, above {pt['psd_above']}; dP {pt['dP']}")
    cells = [(kw, a0) for kw in grid for a0 in (0.0, 0.05, 0.2)]
    with Pool(9) as p: C = [c for c in p.map(cell3, cells) if c is not None]
    H = [c for c in C if c['hyp']]
    print(f"3a-3b: precondition in {len(C)} cells (3a {sum(c['kind'] == '3a' for c in C)}, 3b {sum(c['kind'] == '3b' for c in C)}); hypotheses also hold in {len(H)}")
    print(f"  S_A pinned at the one-review tomorrow {max(c['pinned'] for c in H):.1e}; order {sum(c['order'] for c in H)}/{len(H)}; dynamic tomorrow trades in {min(c['ntr'] for c in H)}-{max(c['ntr'] for c in H)} of 16 states; "
          f"dynamic S_A strictly inside the bracket {sum(bool(c['Sd_inside']) for c in H)}/{len(H)}; root line with the dynamic S_A {max((c['rootline'] for c in H if c['rootline'] is not None), default=0):.1e}")
    for c in [c for c in H if c['kind'] == '3a' and c['traded']][:1] + [c for c in H if c['kind'] == '3b' and c['traded']][:1]:
        if c['traded']: print(f"  {c['kind']} {c['regime'][:5]}: actual threshold g_0 = {c['g0']:+.5f} against the claimed {c['claimed']:+.5f}")
