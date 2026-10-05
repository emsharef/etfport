"""Red's reproduction of experiment 056 (claim 048, many funds and many ETFs), written from the registered Design without reading
experiments/056/run.py or experiments/d16-harness/harness_n.py. Two funds, two frictionless spanning ETFs, two factors, two reviews,
two-point laws per coordinate (16 parameter atoms x 16 shock atoms = 256 states); red's lifted joint program in cvxpy/CLARABEL;
incumbent values from the marking duals (S = sum_z g nu + beta E[g eta_1], red's convention checked in its 055 reproduction).
The registered 32 cells, and Deviation 1's 8 supplementary cells reported separately. Run: uv run python experiments/056/red_reproduce.py"""
import itertools, numpy as np, cvxpy as cp, warnings
from multiprocessing import Pool
warnings.simplefilter('ignore'); GAM, BETA, BP = 5.0, 1.0, 1e4; NF, K = 2, 2; n = NF + K
SOLV = dict(solver=cp.CLARABEL, tol_gap_abs=1e-12, tol_gap_rel=1e-12, tol_feas=1e-12, max_iter=500)
PRE = {"equity-style": dict(alpha=-0.0019, fund=0.0050), "fixed-income-style": dict(alpha=0.0020, fund=0.0020)}
BE = np.array([[1.0, 0.0], [0.5, 1.0]]); BA = np.array([[1.0, 0.3], [0.6, 0.8]]); B = np.vstack([BA, BE]); R = np.linalg.inv(BE)
LAM, SL, SF = np.array([0.015, 0.005]), np.array([0.005, 0.005]), np.array([0.08, 0.04])


def build(regime, start, cash, rev=1.0, alpha1=None, cap=0.25, V=None):
    P = PRE[regime]; sA = np.array([0.02, 0.02]); am = np.array([P['alpha'], P['alpha'] / 2]) if alpha1 is None else np.array([alpha1, alpha1 / 2])
    pa = np.full(2, 0.0035 ** 2); v0 = pa ** 2 / (pa + sA ** 2)
    target = rev * v0 if V is None else np.full(2, V); pa = (target + np.sqrt(target ** 2 + 4 * target * sA ** 2)) / 2
    kp = np.array([P['fund'], P['fund'] * 1.5, 0.0, 0.0]); km = kp.copy()
    pl = SL ** 2; kl = pl / (pl + SF ** 2); ka = pa / (pa + sA ** 2)
    def mom(lh, ah, pl_, pa_):
        Sf = np.diag(SF ** 2 + pl_); mu = np.concatenate([ah + BA @ lh, BE @ lh])
        return mu, B @ Sf @ B.T + np.diag(np.concatenate([sA ** 2 + pa_, np.zeros(K)])), Sf
    I = dict(v=sA ** 2 + pa, am=am, kp=kp, km=km, cap=np.array([cap, cap, np.inf, np.inf]), x0=np.array(start, float), h=cash)
    I['m0'] = mom(LAM, am, pl, pa); I['Z'] = []
    for sg in itertools.product([-1, 1], repeat=8):
        lam = LAM + np.array(sg[0:2]) * SL; al = am + np.array(sg[2:4]) * np.sqrt(pa); f = lam + np.array(sg[4:6]) * SF; res = al + np.array(sg[6:8]) * sA
        lh = LAM + kl * (f - LAM); ah = am + ka * (res - am)
        I['Z'].append(dict(q=1 / 256, g=np.concatenate([1 + BA @ f + res, 1 + BE @ f]), m=mom(lh, ah, (1 - kl) * pl, (1 - ka) * pa)))
    return I


def spend(x, xm, I): d = x - xm; return d.sum() + I['kp'] @ np.maximum(d, 0) + I['km'] @ np.maximum(-d, 0)


def box(x, I): return [x >= 0, x[:NF] <= I['cap'][:NF]]


def review(mu, S, xm, h, I):
    x = cp.Variable(n); u = cp.Variable(n, nonneg=True); d = cp.Variable(n, nonneg=True); c = I['kp'] @ u + I['km'] @ d; b = h - cp.sum(x - xm) - c >= 0
    cp.Problem(cp.Maximize(BP * (mu @ x - GAM / 2 * cp.quad_form(x, cp.psd_wrap(S)) - c)), [x - xm == u - d, b] + box(x, I)).solve(**SOLV)
    return x.value, float(b.dual_value) / BP


def joint(I):
    x0 = cp.Variable(n); u0 = cp.Variable(n, nonneg=True); d0 = cp.Variable(n, nonneg=True); c0 = I['kp'] @ u0 + I['km'] @ d0; h0 = I['h'] - cp.sum(x0 - I['x0']) - c0
    cons = [x0 - I['x0'] == u0 - d0] + box(x0, I); b0 = h0 >= 0; cons.append(b0); mu0, S0, _ = I['m0']
    obj = mu0 @ x0 - GAM / 2 * cp.quad_form(x0, cp.psd_wrap(S0)) - c0; bs, mk = [], []
    for z in I['Z']:
        x1 = cp.Variable(n); u = cp.Variable(n, nonneg=True); d = cp.Variable(n, nonneg=True); c1 = I['kp'] @ u + I['km'] @ d
        m = x1 - cp.multiply(z['g'], x0) == u - d; cons += [m] + box(x1, I); mk.append(m)
        bb = h0 - cp.sum(x1 - cp.multiply(z['g'], x0)) - c1 >= 0; cons.append(bb); bs.append(bb)
        obj = obj + BETA * z['q'] * (z['m'][0] @ x1 - GAM / 2 * cp.quad_form(x1, cp.psd_wrap(z['m'][1])) - c1)
    cp.Problem(cp.Maximize(BP * obj), cons).solve(**SOLV)
    e0 = float(b0.dual_value) / BP; e1 = np.array([float(bb.dual_value) / BP / (BETA * z['q']) for bb, z in zip(bs, I['Z'])])
    S = sum(z['g'] * np.asarray(m.dual_value) for z, m in zip(I['Z'], mk)) / BP + BETA * sum(z['q'] * z['g'] * e for z, e in zip(I['Z'], e1))
    return x0.value, e0, e1, S


def cell(args):
    kind, kw = args; I = build(**kw); mu0, S0, Sf0 = I['m0']
    x0, e0, e1, S = joint(I); eh = e0 + BETA * e1.mean(); hyp = e0 < 1e-9 and (x0[NF:] > 1e-7).all()
    out = dict(kind=kind, kw=kw, hyp=hyp, reason=('ETF at zero ' if not (x0[NF:] > 1e-7).all() else '') + ('budget binds' if e0 >= 1e-9 else ''), eta_pos=e1.max() > 1e-8)
    if not hyp: return out
    lres = LAM + R @ (S[NF:] - eh); b0 = np.linalg.solve(GAM * Sf0, lres); fx = []
    for i in range(NF):
        r = R.T @ BA[i]; ar = I['am'][i] + S[i] - r @ S[NF:] - eh * (1 - r.sum())
        lo, hi = (ar - (1 + eh) * I['kp'][i]) / (GAM * I['v'][i]), (ar + (1 + eh) * I['km'][i]) / (GAM * I['v'][i])
        fx.append(np.clip(np.clip(I['x0'][i], lo, hi), 0, I['cap'][i]))
    fx = np.array(fx); xE = R.T @ (b0 - BA.T @ fx)
    out['p2'] = max(np.abs(fx - x0[:NF]).max(), np.abs(xE - x0[NF:]).max(), np.abs(b0 - B.T @ x0).max())
    tilt = R @ (S[NF:] - eh); tilt_form = BETA * R @ sum(z['q'] * (z['g'][NF:] - 1) * e for z, e in zip(I['Z'], e1))
    out['frictionless'] = np.abs(tilt - tilt_form).max(); out['tilt'] = np.abs(tilt).max()
    xm0, em0 = review(mu0, S0, I['x0'], I['h'], I)
    if em0 < 1e-9 and (xm0[NF:] > 1e-7).all():
        lhs = x0[NF:] - xm0[NF:]; rhs = R.T @ np.linalg.solve(GAM * Sf0, R @ (S[NF:] - eh)) - R.T @ BA.T @ (x0[:NF] - xm0[:NF])
        out['p3'] = np.abs(lhs - rhs).max()
    return out


if __name__ == "__main__":
    starts = [(0, 0, 0.6, 0.3), (0.15, 0.15, 0.1, 0.05), (0.22, 0.10, 0.3, 0.1), (0.05, 0.05, 0.4, 0.2)]
    reg = [('reg', dict(regime=r, start=s, cash=c, rev=v)) for r in PRE for s in starts for c in (0.30, 0.02) for v in (1.0, 4.0)]
    sup = [('sup', dict(regime='equity-style', start=(0, 0, 0.3, 0.2), cash=c, alpha1=a, cap=1.0, V=V)) for a in (0.004, 0.006) for V in (4e-5, 8e-5) for c in (0.30, 0.50)]
    with Pool(9) as p: O = p.map(cell, reg + sup)
    for kind, name in (('reg', 'registered (32)'), ('sup', "Deviation 1's supplementary (8, post hoc)")):
        C = [o for o in O if o['kind'] == kind]; H = [o for o in C if o['hyp']]
        print(f"{name}: hypotheses hold at {len(H)}; fail at {len(C) - len(H)} (ETF at zero {sum('ETF' in o['reason'] for o in C if not o['hyp'])}, today's budget binding {sum('budget' in o['reason'] for o in C if not o['hyp'])})")
        if H:
            P3 = [o['p3'] for o in H if 'p3' in o]
            print(f"  part 2 separated root: largest error {max(o['p2'] for o in H):.1e}; part 3 identity at {len(P3)} cells, largest {max(P3) if P3 else float('nan'):.1e}; "
                  f"frictionless form {max(o['frictionless'] for o in H):.1e}; cells with eta_1 > 0: {sum(o['eta_pos'] for o in H)}, largest tilt {max(o['tilt'] for o in H):.1e}")
