"""Red's reproduction of experiment 027 (regime map), written from the registered Design and Deviations 1-2,
without reading run.py or report.py. FF5 factors via red's experiment 022 reproduction (pinned file,
SHA-256 checked). Deterministic first-quarter quantities ((a)-(d) at t = 0) are computed exactly; Monte
Carlo only at the anchors, with red's own seeds.

Usage: uv run python experiments/027/red_reproduce.py <ff5 zip> det
       uv run python experiments/027/red_reproduce.py <ff5 zip> mc <R> <procs>
"""
import importlib.util, os, sys, itertools
import numpy as np
import cvxpy as cp
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("r22", os.path.join(HERE, "..", "022", "red_reproduce.py"))
r22 = importlib.util.module_from_spec(spec); spec.loader.exec_module(r22)
GAM, T, N, K = 5.0, 20, 6, 3
FCAP, ECAP = 0.25, 1.0
EQ = dict(a=-0.19, s=0.35, sA=2.0, r=10, lE=0.01, rho=1.0, f=1, D=1, menu='full')
FI = dict(a=0.20, s=0.35, sA=1.0, r=0.5, lE=0.1, rho=1.0, f=10, D=1, menu='missing')
Q = None


def base(zp):
    Qf = r22.factors(zp)[:, :3]
    rng = np.random.default_rng(2027)
    BA = np.column_stack([rng.uniform(0.85, 1.15, N), rng.normal(0, 0.3, (N, 2))])
    return dict(lam_hat=Qf.mean(0), Sf=np.cov(Qf.T), BA=BA)


def instance(B, c):
    BEf = np.array([[1, 0, 0], [1, .8, .2], [1, 0, .6]], float)
    BE = BEf if c['menu'] == 'full' else BEf[:2]
    M = BE.shape[0]; n = N + M
    s = c['s'] / 100; sb = s / 5; sA = c['sA'] / 100
    P0 = np.zeros((K + N, K + N)); P0[:K, :K] = B['Sf'] / 248 * c['D']
    P0[K:, K:] = sb ** 2 * np.ones((N, N)) + (s ** 2 - sb ** 2) * np.eye(N)
    m0 = np.r_[B['lam_hat'], np.full(N, c['a'] / 100)]
    G = np.zeros((n, K + N)); G[:N, :K] = B['BA']; G[N:, :K] = BE; G[:N, K:] = np.eye(N)
    Bm = np.vstack([B['BA'], BE])
    Sr = Bm @ B['Sf'] @ Bm.T + np.diag(np.r_[np.full(N, sA ** 2), np.full(M, 0.003 ** 2)])
    cE = np.full(M, c['f'] * 1e-4)
    lam = np.r_[np.full(N, c['r'] * c['lE']), np.full(M, c['lE'])]
    rho = c['rho']; phi = np.r_[np.ones(K), np.full(N, rho)]
    Qs = np.zeros((K + N, K + N)); Qs[K:, K:] = (1 - rho ** 2) * P0[K:, K:]
    Rn = np.zeros((K + N, K + N)); Rn[:K, :K] = B['Sf']; Rn[K:, K:] = sA ** 2 * np.eye(N)
    P = [P0]; Pp = []
    for t in range(T + 8):
        pp = np.linalg.inv(np.linalg.inv(P[-1]) + np.linalg.inv(Rn)); Pp.append(pp)
        P.append(np.diag(phi) @ pp @ np.diag(phi) + Qs)
    Sig = [G @ P[t] @ G.T + Sr for t in range(T + 8)]
    starts = {'all-ETF': np.r_[np.zeros(N), 0.9, np.zeros(M - 1)], 'all-fund': np.r_[np.full(N, 0.15), np.zeros(M)],
              'mixed': np.r_[np.full(N, 0.075), 0.45, np.zeros(M - 1)]}
    return dict(M=M, n=n, G=G, Bm=Bm, BE=BE, Sr=Sr, cE=cE, lam=lam, phi=phi, Qs=Qs, Rn=Rn, P=P, Pp=Pp, Sig=Sig,
                P0=P0, m0=m0, starts=starts, g0=np.r_[np.zeros(N), -cE], tb=m0.copy(), Sf=B['Sf'])


def chol(A): return np.linalg.cholesky(A + 1e-14 * np.eye(len(A))).T


class Prog:
    def __init__(self, I, H, mode=None, fibre=False):
        n, M = I['n'], I['M']; lam = I['lam']
        self.xp = cp.Parameter(n); self.mu = [cp.Parameter(n) for _ in range(H)]; self.C = [cp.Parameter((n, n)) for _ in range(H)]
        self.X = cp.Variable((n, H)); cap = np.r_[np.full(N, FCAP), np.full(M, ECAP)]
        obj, cons, prev = 0, [], self.xp
        for k in range(H):
            x = self.X[:, k]; u = x - prev; q = cp.sum(cp.multiply(lam, cp.square(u)))
            obj += x @ self.mu[k] - GAM / 2 * cp.sum_squares(self.C[k] @ x) - 0.5 * q
            cons += [x >= 0, x <= cap, cp.sum(x) + 0.5 * q <= 1]
            if mode == 'etf-only': cons.append(u[:N] <= 0)
            if mode == 'funds-only': cons.append(u[N:] <= 0)
            prev = x
        if fibre: self.b = cp.Parameter(K); cons.append(I['Bm'].T @ self.X[:, 0] == self.b)
        self.p = cp.Problem(cp.Maximize(obj), cons)

    def solve(self, xp, mus, Cs, b=None):
        self.xp.value = xp
        for a, v in zip(self.mu, mus): a.value = v
        for a, v in zip(self.C, Cs): a.value = v
        if b is not None: self.b.value = b
        self.p.solve(solver=cp.CLARABEL); return np.maximum(self.X.value[:, 0], 0)


class Stage1:
    def __init__(self, I):
        n, M = I['n'], I['M']; lam = I['lam']
        self.xp = cp.Parameter(n); self.lh = cp.Parameter(K); self.C = cp.Parameter((K, K))
        x = cp.Variable(n); u = x - self.xp; q = cp.sum(cp.multiply(lam, cp.square(u))); b = I['Bm'].T @ x
        cap = np.r_[np.full(N, FCAP), np.full(M, ECAP)]; self.x = x; self.Bm = I['Bm']
        self.p = cp.Problem(cp.Maximize(b @ self.lh - GAM / 2 * cp.sum_squares(self.C @ b) - 1e-9 * cp.sum_squares(u)),
                            [x >= 0, x <= cap, cp.sum(x) + 0.5 * q <= 1])

    def solve(self, xp, lh, Cf):
        self.xp.value = xp; self.lh.value = lh; self.C.value = Cf; self.p.solve(solver=cp.CLARABEL)
        return self.Bm.T @ self.x.value


def first_quarter(I, progs, xs, m, t=0, which=('L', 'S', 'rule', 'ts')):
    H = min(8, T - t); C = [chol(I['Sig'][t + k]) for k in range(H)]
    fc = [I['G'] @ (I['phi'] ** k * m + (1 - I['phi'] ** k) * I['tb']) + I['g0'] for k in range(H)]
    out = {}
    if 'L' in which: out['L'] = progs[('L', H)].solve(xs, fc, C)
    if 'S' in which: out['S'] = progs[('L', H)].solve(xs, fc, [C[0]] * H)
    if 'rule' in which: out['rule'] = progs[('L', 1)].solve(xs, fc[:1], C[:1])
    if 'ts' in which:
        b = progs['s1'].solve(xs, m[:K], chol(I['Sf'] + I['P'][t][:K, :K]))
        out['ts'] = progs['fib'].solve(xs, fc[:1], C[:1], b=b)
    if 'etf' in which: out['etf'] = progs[('etf', H)].solve(xs, fc, C)
    if 'fund' in which: out['fund'] = progs[('fund', H)].solve(xs, fc, C)
    return out


def make_progs(I):
    pr = {}
    for H in range(1, 9):
        pr[('L', H)] = Prog(I, H); pr[('etf', H)] = Prog(I, H, 'etf-only'); pr[('fund', H)] = Prog(I, H, 'funds-only')
    pr['s1'] = Stage1(I); pr['fib'] = Prog(I, 1, fibre=True)
    return pr


def det(B):
    rows = []
    for anc_name, anc in (('EQ', EQ), ('FI', FI)):
        # S1: a x r; counts bought from all-ETF / sold from all-fund; first-trade L1 MPC-L vs rule; two-stage exactness
        print(f'S1 {anc_name}: funds bought from all-ETF / sold from all-fund (MPC-L, t = 0)')
        for a in (-0.4, -0.2, 0.0, 0.2, 0.4):
            line = []
            for r in (0.5, 1, 2, 10):
                c = dict(anc, a=a, r=r); I = instance(B, c); pr = make_progs(I)
                oE = first_quarter(I, pr, I['starts']['all-ETF'], I['m0']); oF = first_quarter(I, pr, I['starts']['all-fund'], I['m0'])
                nb = int(np.sum(oE['L'][:N] - I['starts']['all-ETF'][:N] > 0.001)); ns = int(np.sum(oF['L'][:N] - I['starts']['all-fund'][:N] < -0.001))
                line.append(f'{nb}/{ns}')
                for st in ('all-ETF', 'all-fund'):
                    o = oE if st == 'all-ETF' else oF
                    rows.append((anc_name, 'S1', a, r, st, np.abs(o['L'] - o['rule']).sum(), np.abs(o['L'] - o['S']).sum(), np.abs(o['ts'] - o['rule']).sum()))
            print(f'  a {a:+.1f}: ' + ', '.join(line))
        # S3: premium sensitivity (rule, mixed start): largest L1 change in fund holdings per prior SD along a factor
        print(f'S3 {anc_name}: premium sensitivity (L1 of fund holdings per prior SD, rule, mixed start)')
        for menu in ('full', 'missing'):
            vals = []
            for D in (1, 4, 16):
                c = dict(anc, menu=menu, D=D); I = instance(B, c); pr = make_progs(I)
                base_x = first_quarter(I, pr, I['starts']['mixed'], I['m0'], which=('rule',))['rule']
                sd = np.sqrt(np.diag(I['P0'][:K, :K])); worst = 0
                for k in range(K):
                    for sgn in (1, -1):
                        m = I['m0'].copy(); m[k] += sgn * sd[k]
                        x = first_quarter(I, pr, I['starts']['mixed'], m, which=('rule',))['rule']
                        worst = max(worst, np.abs(x[:N] - base_x[:N]).sum())
                vals.append(worst)
            print(f'  {menu}: ' + ', '.join(f'{v:.4f}' for v in vals))
    L1 = [r[5] for r in rows]; LS = [r[6] for r in rows]; TS = [r[7] for r in rows]
    print(f'S1 first-trade L1(MPC-L, rule): {min(L1):.3f}-{max(L1):.3f}; L1(MPC-L, MPC-S) max {max(LS):.2e}; two-stage exact (L1 < 1e-6) in {sum(x < 1e-6 for x in TS)}/{len(TS)}')


_CACHE = {}


def path_mc(args):
    zp, anc_name, st, r = args
    if anc_name not in _CACHE:
        B = base(zp); c = EQ if anc_name == 'EQ' else FI; I = instance(B, c); _CACHE[anc_name] = (I, make_progs(I))
    I, pr = _CACHE[anc_name]
    rng = np.random.default_rng((9027, 0 if anc_name == 'EQ' else 1, r))
    th = rng.multivariate_normal(I['m0'], I['P0'])
    zf = rng.multivariate_normal(np.zeros(K), I['Sf'], size=T); zA = rng.normal(size=(T, N)) * np.sqrt(I['Rn'][K, K])
    eta = rng.normal(size=(T, N)); Lq = np.linalg.cholesky(I['Qs'][K:, K:] + 1e-30 * np.eye(N)) if I['Qs'].any() else np.zeros((N, N))
    names = ['L', 'S', 'rule', 'ts', 'etf', 'fund']
    x = {k: I['starts'][st].copy() for k in names}; tot = {k: 0.0 for k in names}; m = I['m0'].copy()
    for t in range(T):
        new = {}
        for k in names:
            new[k] = first_quarter(I, pr, x[k], m, t=t, which=(k,))[k]
        mu_true = I['G'] @ th + I['g0']
        for k in names:
            xx = new[k]; u = xx - x[k]
            tot[k] += xx @ mu_true - GAM / 2 * xx @ I['Sr'] @ xx - 0.5 * np.sum(I['lam'] * u * u); x[k] = xx
        y = np.r_[th[:K] + zf[t], th[K:] + zA[t]]
        mp = I['Pp'][t] @ (np.linalg.solve(I['P'][t], m) + np.linalg.solve(I['Rn'], y))
        m = I['phi'] * mp + (1 - I['phi']) * I['tb']
        th = np.r_[th[:K], I['phi'][K:] * th[K:] + (1 - I['phi'][K:]) * I['tb'][K:] + Lq @ eta[t]]
    return anc_name, st, {k: tot[k] / T * 1e4 for k in names}


if __name__ == '__main__':
    ZP = sys.argv[1]
    if sys.argv[2] == 'det':
        det(base(ZP))
    else:
        R, procs = int(sys.argv[3]), int(sys.argv[4])
        jobs = [(ZP, a, s, r) for a in ('EQ', 'FI') for s in ('all-ETF', 'all-fund', 'mixed') for r in range(R)]
        with Pool(procs) as pool:
            res = pool.map(path_mc, jobs)
        se = lambda v: np.std(v, ddof=1) / np.sqrt(len(v))
        for a in ('EQ', 'FI'):
            for s in ('all-ETF', 'all-fund', 'mixed'):
                ce = {k: np.array([q[2][k] for q in res if q[0] == a and q[1] == s]) for k in ('L', 'S', 'rule', 'ts', 'etf', 'fund')}
                f = lambda o: f"{(ce['L'] - ce[o]).mean():.2f} ({se(ce['L'] - ce[o]):.2f})"
                print(f"{a} {s}: MPC-L minus ETF-only {f('etf')}; funds-only {f('fund')}; rule {f('rule')}; two-stage {f('ts')}; MPC-S {f('S')}")
