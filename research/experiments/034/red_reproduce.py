"""Red's reproduction of experiment 034 (claim 102), written without reading run.py, report.py, checks/102 or fastdp.py.

One review: claim 102's Setting (directional rates on every instrument, caps, funded cash h^-, ETF fees), solved with
cvxpy/CLARABEL, objective in bp; eta is the cash constraint's dual. Instance: the Design's with Deviation 1 (B^E = I_2).
Several reviews: red's own exact one-instrument DP on a holding grid (exact directional L1 transform) and a belief grid.
"""
import sys, warnings
import numpy as np, cvxpy as cp
from multiprocessing import Pool
warnings.simplefilter('ignore')

GAM = 5.0; SF = np.diag([0.08 ** 2, 0.04 ** 2]); PL0 = np.diag([0.005 ** 2] * 2); LAM0 = np.array([0.015, 0.005])
BA = np.array([[1, 0.5], [1, 0.2], [1, -0.3]]); BE = np.eye(2); V = np.full(3, 0.02 ** 2 + 0.0035 ** 2)
B = np.vstack([BA, BE]); N, M, K = 3, 2, 2; n = N + M; BP = 1e4
R = np.linalg.inv(BE)                                   # netting vectors r_i = R' B^A_i' (= B^A_i here)


class Solver:
    def __init__(self, fix_funds=False):
        self.mu = cp.Parameter(n); self.Lb = cp.Parameter((K, n)); self.d = cp.Parameter(n, nonneg=True)
        self.kp = cp.Parameter(n, nonneg=True); self.km = cp.Parameter(n, nonneg=True); self.x0 = cp.Parameter(n)
        self.cap = cp.Parameter(n, nonneg=True); self.h = cp.Parameter()
        x = cp.Variable(n); up = cp.Variable(n, nonneg=True); dn = cp.Variable(n, nonneg=True); self.x = x
        cost = self.kp @ up + self.km @ dn
        Q = self.mu @ x - GAM / 2 * (cp.sum_squares(self.Lb @ x) + cp.sum(cp.multiply(self.d, cp.square(x)))) - cost
        self.cashc = self.h - cp.sum(x - self.x0) - cost >= 0
        cons = [x - self.x0 == up - dn, x >= 0, x <= self.cap, self.cashc]
        if fix_funds: cons.append(x[:N] == self.x0[:N])
        self.pr = cp.Problem(cp.Maximize(BP * Q), cons); self.cost = cost

    def solve(self, I):
        Sft = SF + I['Pl']; Lf = np.linalg.cholesky(Sft)
        self.mu.value = np.concatenate([I['ah'] + BA @ I['lam'], BE @ I['lam'] - I['cE']])
        self.Lb.value = Lf.T @ B.T; self.d.value = np.concatenate([V, I['sE'] ** 2])
        self.kp.value = I['kp']; self.km.value = I['km']; self.x0.value = I['x0']; self.cap.value = I['cap']; self.h.value = I['h']
        self.pr.solve(solver=cp.CLARABEL, tol_gap_abs=1e-12, tol_gap_rel=1e-12, tol_feas=1e-12, max_iter=400)
        x = self.x.value.copy(); eta = float(self.cashc.dual_value) / BP
        cash = I['h'] - np.sum(x - I['x0']) - float(I['kp'] @ np.maximum(x - I['x0'], 0) + I['km'] @ np.maximum(I['x0'] - x, 0))
        Sig = B @ Sft @ B.T + np.diag(np.concatenate([V, I['sE'] ** 2]))
        g = self.mu.value - GAM * Sig @ x
        return dict(x=x, eta=eta, cash=cash, g=g, status=self.pr.status)


SOL = {}


def sol(fix=False):
    if fix not in SOL: SOL[fix] = Solver(fix)
    return SOL[fix]


def base(**kw):
    x0A = np.array([0.0, 0.1, 0.1]); Sft = SF + PL0
    I = dict(ah=np.array([0.0, GAM * V[1] * 0.1, GAM * V[2] * 0.1]), lam=LAM0.copy(), Pl=PL0.copy(), sE=np.zeros(M),
             cE=np.zeros(M), kp=np.array([0.002] * 3 + [0, 0]), km=np.array([0.002] * 3 + [0, 0]), cap=np.array([0.25] * 3 + [1, 1]), h=1.0)
    I.update(kw)
    xA0 = I.get('xA0', x0A)
    if 'xE0' not in I:
        y = np.linalg.solve(GAM * (SF + PL0), LAM0)          # base premium's remainder
        I['xE0'] = np.clip(R.T @ (y - BA.T @ xA0), 0, 1)
    I['x0'] = np.concatenate([xA0, I['xE0']])
    return I


def interior(r, I, tolE=1e-5):
    xE = r['x'][N:]
    return bool(np.all(xE > tolE) and np.all(xE < I['cap'][N:] - tolE))


# ---------------- curve 1: part 3's strip ----------------
def c1_job(a):
    rates, x1, a1 = a
    I = base(xA0=np.array([x1, 0.1, 0.1])); I['ah'][0] = a1; I['kp'][0], I['km'][0] = rates
    r = sol().solve(I); return rates, x1, a1, r, interior(r, I) and r['cash'] > 1e-7, I


def curve1(pool):
    jobs = [(rt, x1, a1) for rt in [(0.002, 0.002), (0.005, 0.001), (0.0, 0.0)] for x1 in np.linspace(0, 0.25, 26) for a1 in np.linspace(-0.01, 0.01, 81)]
    res = pool.map(c1_job, jobs, chunksize=50)
    agree = tot = edge = 0; herr = eerr = 0; outside = 0; p1bad = 0
    y = np.linalg.solve(GAM * (SF + PL0), LAM0)
    for (kp, km), x1, a1, r, hyp, I in res:
        if not hyp: outside += 1; continue
        c = GAM * V[0]; m = a1 - c * x1
        if min(abs(m - kp), abs(m + km)) < 1e-9: edge += 1; continue
        pred = 1 if (m > kp and x1 < 0.25) else (-1 if (m < -km and x1 > 0) else 0)
        dx = r['x'][0] - x1; got = 1 if dx > 1e-5 else (-1 if dx < -1e-5 else 0)
        tot += 1; agree += pred == got
        clip = min(max(x1, (a1 - kp) / c), (a1 + km) / c); clip = min(max(clip, 0), 0.25)
        herr = max(herr, abs(r['x'][0] - clip)); eerr = max(eerr, np.abs(r['x'][N:] - R.T @ (y - BA.T @ r['x'][:N])).max())
        p1bad += not part1_ok(r, I)
    print(f"curve 1: {tot} points off edges meet hypotheses ({edge} on an edge, {outside} outside): strip agreement {agree}/{tot}; "
          f"|x_1 - clip| max {herr:.1e}; |x^E - R'(y* - B^A' x^A)| max {eerr:.1e}; part 1 criterion failures {p1bad}")


def c1p_job(a):
    x1, a1 = a; out = []
    for lam in [np.array(v) for v in [(-0.01, 0.0), (0.0, 0.02), (0.015, 0.005), (0.03, -0.005), (0.04, 0.04)]]:
        for sc in [0.2, 1.0, 5.0]:
            Pl = PL0 * sc ** 2; y = np.linalg.solve(GAM * (SF + Pl), lam)
            I = base(xA0=np.array([x1, 0.1, 0.1]), lam=lam, Pl=Pl, xE0=np.clip(R.T @ (y - BA.T @ np.array([x1, 0.1, 0.1])), 0, 1)); I['ah'][0] = a1
            r = sol().solve(I)
            if interior(r, I) and r['cash'] > 1e-7: out.append(r['x'][0])
    return (max(out) - min(out)) if len(out) > 1 else 0.0, len(out)


def curve1_premia(pool):
    res = pool.map(c1p_job, [(x1, a1) for x1 in np.linspace(0, 0.25, 11) for a1 in np.linspace(-0.01, 0.01, 21)])
    print(f"curve 1 premia: {len(res)} plane points x 15 premium settings ({sum(k for _, k in res)} solves meeting hypotheses): largest fund-1 holding change {max(d for d, _ in res):.1e}")


# ---------------- part 1 criterion ----------------
def part1_ok(r, I, tol=2e-7):
    x, g, eta = r['x'], r['g'], max(r['eta'], 0.0)
    for i in range(n):
        dx = x[i] - I['x0'][i]; kp, km = I['kp'][i], I['km'][i]
        if dx > 1e-6: lo = hi = eta + (1 + eta) * kp
        elif dx < -1e-6: lo = hi = eta - (1 + eta) * km
        else: lo, hi = eta - (1 + eta) * km, eta + (1 + eta) * kp
        if x[i] < 1e-7: lo = -np.inf                       # at zero: R_i <= 0 allowed
        if x[i] > I['cap'][i] - 1e-7: hi = np.inf          # at cap: R_i >= 0 allowed
        if not (lo - tol <= g[i] <= hi + tol): return False
    return True


# ---------------- onset root ----------------
def onset(I, sign=+1, lo=-0.03, hi=0.03, it=48, det=2e-6):
    """alpha_hat_1 at which fund 1 starts to be bought (sign +1) or sold (sign -1)."""
    def traded(a):
        J = dict(I); J['ah'] = I['ah'].copy(); J['ah'][0] = a; r = sol().solve(J)
        return (sign * (r['x'][0] - I['x0'][0]) > det), r
    if sign > 0:
        if traded(lo)[0] or not traded(hi)[0]: return None
        for _ in range(it):
            m = (lo + hi) / 2
            if traded(m)[0]: hi = m
            else: lo = m
        return hi, traded(hi)[1], traded(lo)[1]
    else:
        if traded(hi)[0] or not traded(lo)[0]: return None
        for _ in range(it):
            m = (lo + hi) / 2
            if traded(m)[0]: lo = m
            else: hi = m
        return lo, traded(lo)[1], traded(hi)[1]


# ---------------- curve 2: part 4's bracket ----------------
def c2_job(a):
    kE, fee, x1, l1 = a
    I = base(xA0=np.array([x1, 0.1, 0.1]), lam=np.array([l1, 0.005]), cE=np.full(2, fee))
    I['kp'][N:] = kE; I['km'][N:] = kE
    o = onset(I, +1)
    if o is None: return a, None
    a1, r_on, r_below = o
    ok = all(interior(r, I) and r['cash'] > 1e-7 for r in (r_on, r_below))
    r1 = BA[0] @ R          # r_1 = R' B^A_1'
    hp = np.sum(np.maximum(r1, 0) * I['km'][N:] + np.maximum(-r1, 0) * I['kp'][N:])
    hm = np.sum(np.maximum(r1, 0) * I['kp'][N:] + np.maximum(-r1, 0) * I['km'][N:])
    A = a1 + r1 @ I['cE'] - GAM * V[0] * x1
    kp = I['kp'][0]
    dE = r_on['x'][N:] - I['xE0']; dEb = r_below['x'][N:] - I['xE0']
    trading = np.all(np.abs(dEb) > 1e-6)
    sold_share = np.sum(np.abs(r1) * (dEb < 0)) / np.sum(np.abs(r1))
    return a, dict(ok=ok, A=A, lo=kp - hm, hi=kp + hp, pos=(A - (kp - hm)) / (hp + hm) if hp + hm > 0 else None, trading=trading, share=sold_share)


def curve2(pool):
    jobs = [(kE, fee, x1, l1) for kE in [0, 5e-4, 1e-3, 2.5e-3, 5e-3, 1e-2] for fee in [0, 5e-4, 1e-3] for x1 in [0, 0.1] for l1 in [0.005, 0.015, 0.03]]
    res = pool.map(c2_job, jobs, chunksize=4)
    n_ok = bad = 0; z0 = 0; tr = []; idle = []
    for a, d in res:
        if d is None or not d['ok']: continue
        n_ok += 1; bad += not (d['lo'] - 1e-7 <= d['A'] <= d['hi'] + 1e-7)
        if a[0] == 0: z0 = max(z0, abs(d['A'] - d['lo']))
        elif d['trading']: tr.append(abs(d['pos'] - d['share'])); tr_pos = d['pos']
        else: idle.append(d['pos'])
    print(f"curve 2: {n_ok} of {len(jobs)} cells meet hypotheses: outside bracket {bad}; zero ETF rate |A - kappa^+| {z0:.1e}; "
          f"every ETF trading at the onset: {len(tr)} cells, |position - sold share of |r|| max {max(tr) if tr else float('nan'):.1e}; "
          f"idle ETF: {len(idle)} cells, position {min(idle):.2f}-{max(idle):.2f}")


def c2s_job(seed):
    rng = np.random.default_rng([2034, 0, seed])
    x1 = rng.uniform(0, 0.25); I = base(xA0=np.array([x1, rng.uniform(0, 0.25), rng.uniform(0, 0.25)]),
                                        lam=rng.uniform(0.0, 0.03, 2), cE=rng.uniform(0, 1e-3, 2), xE0=rng.uniform(0.2, 0.8, 2))
    I['ah'] = rng.uniform(-0.01, 0.01, 3); I['kp'] = np.concatenate([rng.uniform(0, 0.01, 3), rng.uniform(0, 0.005, 2)])
    I['km'] = np.concatenate([rng.uniform(0, 0.01, 3), rng.uniform(0, 0.005, 2)])
    r = sol().solve(I)
    if not (interior(r, I) and r['cash'] > 1e-7): return None
    out = []
    for i in range(N):
        ri = BA[i] @ R; hp = np.sum(np.maximum(ri, 0) * I['km'][N:] + np.maximum(-ri, 0) * I['kp'][N:]); hm = np.sum(np.maximum(ri, 0) * I['kp'][N:] + np.maximum(-ri, 0) * I['km'][N:])
        A0 = I['ah'][i] + ri @ I['cE'] - GAM * V[i] * I['x0'][i]; dx = r['x'][i] - I['x0'][i]
        if A0 > I['kp'][i] + hp and I['x0'][i] < I['cap'][i]: out.append(('buy', dx > 1e-6))
        if A0 < -I['km'][i] - hm and I['x0'][i] > 0: out.append(('sell', dx < -1e-6))
    return out


def curve2_suff(pool):
    res = [r for r in pool.map(c2s_job, range(500)) if r is not None]
    cases = [c for r in res for c in r]
    print(f"curve 2 sufficient conditions: {len(res)} of 500 draws meet hypotheses; {len(cases)} cases "
          f"({sum(c[0] == 'buy' for c in cases)} buys, {sum(c[0] == 'sell' for c in cases)} sells); violations {sum(not c[1] for c in cases)}")


# ---------------- curve 3: part 5(a), binding budget ----------------
def c3_job(a):
    name, h, side = a
    a1, kf, kE = (-0.0019, 0.005, 0.0) if name == 'equity' else (0.002, 0.002, 0.0)
    x1 = 0.0 if side > 0 else 0.1
    I = base(xA0=np.array([x1, 0.1, 0.1]), xE0=np.zeros(2), h=h); I['kp'][:N] = kf; I['km'][:N] = kf
    o = onset(I, side, lo=-0.05, hi=0.05)
    if o is None: return a, None
    at, r_on, r_near = o
    if not (interior(r_near, I, 1e-6) and r_near['eta'] > 1e-6): return a, dict(skip=True, eta=r_near['eta'], xE=r_near['x'][N:])
    eta = r_near['eta']; s1 = 1 - np.sum(BA[0] @ R); m = at - GAM * V[0] * x1; k = kf
    lit = eta + side * (1 + eta) * k; net = eta * s1 + side * (1 + eta) * k
    return a, dict(skip=False, m=m, lit=lit, net=net, eta=eta)


def curve3(pool):
    jobs = [(nm, h, sd) for nm in ['equity', 'fixed-income'] for h in [0.3, 0.2, 0.1, 0.05, 0.02, 0.01, 0.005, 0.002] for sd in [+1, -1]]
    res = pool.map(c3_job, jobs, chunksize=2)
    good = [(a, d) for a, d in res if d is not None and not d['skip']]
    lit = [abs(d['m'] - d['lit']) for _, d in good]; net = [abs(d['m'] - d['net']) for _, d in good]
    etas = [d['eta'] for _, d in good]
    print(f"curve 3: {len(good)} binding cases with interior ETFs (eta {min(etas):.1e}-{max(etas):.1e}): literal form misses {min(lit) * BP:.1f}-{max(lit) * BP:.1f} bp; "
          f"netted form eta (1 - sum r) +- (1 + eta) kappa max miss {max(net):.1e}")
    ex = good[0]; print(f"  e.g. {ex[0]}: observed {ex[1]['m'] * BP:.1f} bp, literal {ex[1]['lit'] * BP:.1f} bp, netted {ex[1]['net'] * BP:.1f} bp")


# ---------------- curve 4: parts 1 and 2, random draws ----------------
def eta_interval(r, I, idx):
    """eta >= 0 compatible with part 1's lines for instruments idx at r (claim 009 style)."""
    lo, hi = 0.0, np.inf
    if r['cash'] > 1e-8: return (0.0, 0.0)
    x, g = r['x'], r['g']
    for j in idx:
        kp, km = I['kp'][j], I['km'][j]; dx = x[j] - I['x0'][j]
        # line: g - eta - (1 + eta) t, t in T_j; g in [eta - (1+eta) km, eta + (1+eta) kp] (held) etc.
        up_ok = x[j] < I['cap'][j] - 1e-7; dn_ok = x[j] > 1e-7
        if dx > 1e-6:   # bought: g = eta + (1+eta) kp (or >= at cap)
            e = (g[j] - kp) / (1 + kp)
            lo, hi = max(lo, e - 1e-7 if up_ok else lo), min(hi, e + 1e-7)
        elif dx < -1e-6:
            e = (g[j] + km) / (1 - km)
            lo, hi = max(lo, e - 1e-7), min(hi, e + 1e-7 if dn_ok else hi)
        else:
            if up_ok: lo = max(lo, (g[j] - kp) / (1 + kp) - 1e-7)
            if dn_ok: hi = min(hi, (g[j] + km) / (1 - km) + 1e-7)
    return (lo, hi)


def c4_job(seed):
    rng = np.random.default_rng([2034, 1, seed])
    I = base(xA0=rng.uniform(0, 0.25, 3), lam=rng.uniform(-0.01, 0.04, 2), cE=rng.uniform(0, 1e-3, 2), xE0=rng.choice([0.0, 0.3, 0.9, 1.0], 2), h=rng.choice([1.0, 0.05, 0.01]))
    I['ah'] = rng.uniform(-0.01, 0.01, 3); I['kp'] = np.concatenate([rng.uniform(0, 0.01, 3), rng.uniform(0, 0.005, 2)]); I['km'] = I['kp'] * rng.uniform(0.5, 1.5, n)
    r = sol().solve(I); rE = sol(True).solve(I)
    atb = bool(np.any(r['x'][N:] < 1e-6) or np.any(r['x'][N:] > 1 - 1e-6)); bind = r['eta'] > 1e-7
    p1 = part1_ok(r, I)
    lo, hi = eta_interval(rE, I, range(N, n))
    # funds' held condition at x_E as an eta interval
    for i in range(N):
        kp, km = I['kp'][i], I['km'][i]; g = rE['g'][i]; x = rE['x'][i]
        if x < I['cap'][i] - 1e-7: lo = max(lo, (g - kp) / (1 + kp) - 1e-7)
        if x > 1e-7: hi = min(hi, (g + km) / (1 - km) + 1e-7)
    test_none = lo <= hi
    none = bool(np.all(np.abs(r['x'][:N] - I['x0'][:N]) < 1e-6))
    return dict(atb=atb, bind=bind, p1=p1, agree=test_none == none, none=none)


def curve4(pool):
    res = pool.map(c4_job, range(300))
    print(f"curve 4: 300 draws ({sum(d['atb'] for d in res)} with an ETF at a bound, {sum(d['bind'] for d in res)} binding budget): part 1 failures {sum(not d['p1'] for d in res)}; "
          f"part 2 test agrees with the full solve at {sum(d['agree'] for d in res)}/300 ({sum(d['none'] for d in res)} no-trade)")


# ---------------- curve 5: part 6, exact one-instrument DP ----------------
def dp_cell(args):
    beta, T, k, p0r = args
    sA2 = 0.02 ** 2; p0 = p0r * sA2; p = [1 / (1 / p0 + t / sA2) for t in range(T + 1)]
    cap = 1.0; nx = 2001; xs = np.linspace(0, cap, nx); hx = xs[1] - xs[0]
    sdt = np.sqrt(p0 - p[T]); mg = np.linspace(-(4 * sdt + 3 * k), 4 * sdt + 3 * k, 801)
    gx, gw = np.polynomial.hermite_e.hermegauss(40); gw = gw / gw.sum()
    Vn = np.zeros((len(mg), nx)); out = []
    for t in reversed(range(T)):
        c = GAM * (sA2 + p[t])
        if t < T - 1:
            q = np.sqrt(p[t] - p[t + 1]); EV = np.zeros_like(Vn)
            for z, w in zip(gx, gw):
                mp = np.clip(mg + q * z, mg[0], mg[-1]); j = np.clip(np.searchsorted(mg, mp) - 1, 0, len(mg) - 2)
                a = ((mp - mg[j]) / (mg[j + 1] - mg[j]))[:, None]
                EV += w * ((1 - a) * Vn[j] + a * Vn[j + 1])
        else:
            EV = np.zeros_like(Vn)
        W = mg[:, None] * xs[None, :] - c / 2 * xs[None, :] ** 2 + beta * EV
        # V(x_) = max_y W(y) - k (y - x_)^+ - k (x_ - y)^+ (symmetric rates here)
        f = np.maximum.accumulate(W + k * xs, axis=1) - k * xs                    # y <= x_
        b = np.flip(np.maximum.accumulate(np.flip(W - k * xs, 1), axis=1), 1) + k * xs   # y >= x_
        Vt = np.maximum(f, b)
        # purchase threshold from zero: D(m) = (W(h) - W(0))/h - k crosses 0
        D = (W[:, 1] - W[:, 0]) / hx - k
        i = np.where(np.diff(np.sign(D)) > 0)[0][0]; thr = mg[i] - D[i] * (mg[i + 1] - mg[i]) / (D[i + 1] - D[i])
        # band vs one-review band on rows within 2 SD of the prior mean
        rows = np.where(np.abs(mg) <= 2 * sdt + 3 * k)[0]; ex = 0.0; last = 0.0
        for rI in rows[::8]:
            hold = Vt[rI] - W[rI] <= 1e-13   # held iff staying is optimal
            xs_h = xs[hold]
            if len(xs_h) == 0: continue
            lo1 = min(max((mg[rI] - k) / c, 0), cap); hi1 = max(min((mg[rI] + k) / c, cap), 0)
            ex = max(ex, lo1 - xs_h.min() if xs_h.min() > 0 else 0, xs_h.max() - hi1 if xs_h.max() < cap else 0)
            if t == T - 1: last = max(last, abs(xs_h.min() - lo1) if xs_h.min() > 0 else 0, abs(xs_h.max() - hi1) if xs_h.max() < cap else 0)
        out.append((t, thr, ex, last))
        Vn = Vt
    return args, out, hx


def curve5(pool):
    cells = [(b, T, k, p) for b in [0.9, 0.95, 0.99, 1.0] for T in [2, 4, 8, 20] for k in [0.001, 0.005] for p in [0.03, 0.3]]
    res = pool.map(dp_cell, cells)
    npairs = inb = 0; pos = []; ex = 0; last = 0; hx = res[0][2]
    for (b, T, k, p), out, _ in res:
        for t, thr, e, l in out:
            npairs += 1; lo, hi = (1 - b) * k, k + b * k
            inb += lo - 1e-9 <= thr <= hi + 1e-9; pos.append((thr - lo) / (hi - lo)); ex = max(ex, e); last = max(last, l)
    pos = np.array(pos)
    print(f"curve 5: {npairs} (review, cell) pairs: threshold in [(1-beta) k, k + beta k] at {inb}; position {pos.min():.2f}-{pos.max():.2f}, median {np.median(pos):.2f}; "
          f"band excess over the one-review band {ex:.1e} (grid step {hx:.1e}); last review |band - one-review| {last:.1e}")


if __name__ == "__main__":
    with Pool(9) as pool:
        curve1(pool); curve1_premia(pool); curve2(pool); curve2_suff(pool); curve3(pool); curve4(pool); curve5(pool)
