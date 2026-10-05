"""Red's reproduction of experiment 037 (claim 040), written without reading run.py or report.py.
Instrument-level one-review solver (cvxpy/CLARABEL, bp-scaled; ETFs frictionless with lower bound 0, caps and budget slack),
against claim 040's formulas coded here: w(q) by active-set enumeration, zeta, the fund marginal G, s^Z and the drop-Z rule.
Coordinates: B^E = I, so Q = B^A' (columns r_i), w = x^E + Q x^A, mu_E = lambda_hat - c^E, alpha~ = alpha_hat + Q' c^E."""
import itertools, warnings
import numpy as np, cvxpy as cp
from multiprocessing import Pool
warnings.simplefilter('ignore')
GAM = 5.0; SF = np.diag([0.08 ** 2, 0.04 ** 2]); BP = 1e4
SOLV = dict(solver=cp.CLARABEL, tol_gap_abs=1e-12, tol_gap_rel=1e-12, tol_feas=1e-12, max_iter=500)


def solve(I, fixA=None, free=False, muA=None, muE=None):
    """Joint (or ETF-only at fixed fund holdings) one-review optimum in instrument coordinates."""
    BA, N = I['BA'], len(I['a']); M = BA.shape[1]; S = I['S']; L = np.linalg.cholesky(S)
    xA = cp.Variable(N); xE = cp.Variable(M)
    muA = I['a'] + BA @ I['lam'] if muA is None else muA; muE = I['lam'] - I['cE'] if muE is None else muE
    b = BA.T @ xA + xE
    obj = muA @ xA + muE @ xE - GAM / 2 * (cp.sum_squares(L.T @ b) + cp.sum(cp.multiply(I['V'], cp.square(xA)))) \
        - I['kp'] @ cp.pos(xA - I['x0']) - I['km'] @ cp.pos(I['x0'] - xA)
    cons = [xE <= 10] + ([] if free else [xE >= 0])
    cons += [xA == fixA] if fixA is not None else [xA >= 0, xA <= I['cap']]
    cp.Problem(cp.Maximize(BP * obj), cons).solve(**SOLV)
    return xA.value.copy(), xE.value.copy()


def wq(q, muE, S):
    """argmax muE'w - gam/2 w'Sw s.t. w >= q, by active-set enumeration; returns w, zeta, Z, and the number of valid sets."""
    M = len(q); found = []
    for k in range(M + 1):
        for Z in itertools.combinations(range(M), k):
            Z = list(Z); c = [j for j in range(M) if j not in Z]; w = np.array(q, float)
            if c: w[c] = np.linalg.solve(GAM * S[np.ix_(c, c)], muE[c] - GAM * S[np.ix_(c, Z)] @ q[Z])
            z = GAM * S @ w - muE
            if np.all(w[c] >= q[c] - 1e-13) and np.all(z[Z] >= -1e-13): found.append((w, z, tuple(Z)))
    w, z, Z = found[0]; z = z.copy(); z[[j for j in range(M) if j not in Z]] = 0.0
    return w, z, Z, len(found)


def G(I, xA):
    Q = I['BA'].T; q = Q @ xA; muE = I['lam'] - I['cE']; w, z, Z, nf = wq(q, muE, I['S'])
    at = I['a'] + Q.T @ I['cE']
    return at - GAM * I['V'] * xA - Q.T @ z, Z, z, nf


def sZ(I, Z, i=0):
    S = I['S']; r = I['BA'][i]; Z = list(Z); c = [j for j in range(len(r)) if j not in Z]
    if not Z: return I['V'][i]
    Szc = S[np.ix_(Z, Z)] - (S[np.ix_(Z, c)] @ np.linalg.solve(S[np.ix_(c, c)], S[np.ix_(c, Z)]) if c else 0)
    return I['V'][i] + r[Z] @ Szc @ r[Z]


def draw_random(rng):
    sd = rng.uniform(0.001, 0.01, 2)
    return dict(BA=np.array([[1, 0.5], [1, 0.2], [1, -0.3]]), S=SF + np.diag(sd ** 2), lam=rng.uniform(-0.01, 0.03, 2), cE=rng.uniform(0, 0.002, 2),
                a=rng.uniform(-0.01, 0.01, 3), V=0.02 ** 2 * (1 + rng.uniform(0.01, 3, 3)), kp=rng.uniform(0, 0.02, 3), km=rng.uniform(0, 0.02, 3),
                x0=rng.uniform(0, 0.25, 3), cap=np.full(3, 0.25))


def draw_targeted(rng):
    return dict(BA=np.array([[1, 0.5]]), S=SF + np.diag([0.005 ** 2] * 2), lam=np.array([0.015, rng.uniform(-0.002, 0.005)]), cE=rng.uniform(0, 0.001, 2),
                a=rng.uniform(-0.003, 0.008, 1), V=np.array([0.02 ** 2 + 0.0035 ** 2]), kp=rng.uniform(0, 0.005, 1), km=rng.uniform(0, 0.005, 1),
                x0=rng.uniform(0, 2, 1), cap=np.array([2.0]))


def cls(d, tol=1e-5): return 1 if d > tol else (-1 if d < -tol else 0)


def job_random(k):
    rng = np.random.default_rng([4037, 0, k]); I = draw_random(rng)
    xA, xE = solve(I); g, Z, z, nf = G(I, xA); Zs = tuple(np.where(xE <= 1e-5)[0])
    # solver slacks: -g_E at the optimum
    b = I['BA'].T @ xA + xE; gE = I['lam'] - I['cE'] - GAM * I['S'] @ b
    knife = np.any((xE > 1e-7) & (xE < 1e-5)) or np.any(np.abs(z[list(Z)]) < 1e-9) if Z else np.any((xE > 1e-7) & (xE < 1e-5))
    # part 1 fund lines at the optimum
    ok1 = True
    for i in range(3):
        d = xA[i] - I['x0'][i]; lo, hi = -I['km'][i], I['kp'][i]
        if d > 1e-6: lo = hi = I['kp'][i]
        elif d < -1e-6: lo = hi = -I['km'][i]
        if xA[i] < 1e-6: lo = -np.inf
        if xA[i] > I['cap'][i] - 1e-6: hi = np.inf
        ok1 &= lo - 1e-7 <= g[i] <= hi + 1e-7
    # part 3(a) hold test at the incumbent
    g0, Z0, _, _ = G(I, I['x0']); hold = True
    for i in range(3):
        lo = -np.inf if I['x0'][i] <= 0 else -I['km'][i]; hi = np.inf if I['x0'][i] >= I['cap'][i] else I['kp'][i]
        hold &= lo <= g0[i] <= hi
    none_traded = bool(np.all(np.abs(xA - I['x0']) <= 1e-5))
    # 3(d): premium shift at fixed holdings, e = 1e-4 along each factor
    shifts = []
    for f in range(2):
        for sgn in (1, -1):
            e = np.zeros(2); e[f] = sgn * 1e-4; J = dict(I); J['lam'] = I['lam'] + e
            g2, Z2, _, _ = G(J, xA)
            if Z2 != Z: continue
            Zl = list(Z); c = [j for j in range(2) if j not in Zl]
            BEzc = (e[Zl] - (I['S'][np.ix_(Zl, c)] @ np.linalg.solve(I['S'][np.ix_(c, c)], e[c]) if c else 0)) if Zl else np.zeros(0)
            pred = np.array([I['BA'][i][Zl] @ BEzc if Zl else 0.0 for i in range(3)])
            # the same shift from the solver: re-optimize the ETFs at the fixed fund holdings and read the fund marginal
            xAf, xEf = solve(J, fixA=xA); bf = I['BA'].T @ xA + xEf
            gA = J['a'] + I['BA'] @ J['lam'] - GAM * (I['BA'] @ (I['S'] @ bf)) - GAM * I['V'] * xA
            shifts.append((float(np.abs((g2 - g) - pred).max()), float(np.abs(gA - g2).max()), len(Zl) == 0, float(np.abs(pred).max())))
    # 5(d): fold-in: ETFs free at premiums (alpha~ - Q_Z' zeta_Z, mu_E + zeta)
    fold = None
    if Z:
        Q = I['BA'].T; at = I['a'] + Q.T @ I['cE'] - Q.T @ z; muE = I['lam'] - I['cE'] + z
        muA = at + I['BA'] @ muE        # map back to instruments: mu_A = alpha~' + Q' mu_E'
        xa2, xe2 = solve(I, free=True, muA=muA, muE=muE)
        fold = float(max(np.abs(xa2 - xA).max(), np.abs(xe2 - xE).max()))
    return dict(Zok=(Z == Zs), zerr=float(np.abs(z[list(Z)] + gE[list(Z)]).max()) if Z else 0.0, nf=nf, knife=bool(knife), ok1=bool(ok1),
                hold=(hold == none_traded), nhold=none_traded, shifts=shifts, fold=fold, nZ=len(Z))


def job_targeted(k):
    rng = np.random.default_rng([4037, 3, k]); I = draw_targeted(rng)
    xA, xE = solve(I); x0 = I['x0'][0]
    g0, Z0, _, _ = G(I, I['x0'])
    # buy/sell/hold from G(x^-)
    pred = 1 if (g0[0] > I['kp'][0] and x0 < 2) else (-1 if (g0[0] < -I['km'][0] and x0 > 0) else 0)
    dec_ok = pred == cls(xA[0] - x0)
    # drop-Z rule at Z^- = Z(r x^-)
    s = sZ(I, Z0); Q = I['BA'].T; Zl = list(Z0); c = [j for j in range(2) if j not in Zl]
    muE = I['lam'] - I['cE']; at = I['a'][0] + Q[:, 0] @ I['cE']
    muzc = (muE[Zl] - (I['S'][np.ix_(Zl, c)] @ np.linalg.solve(I['S'][np.ix_(c, c)], muE[c]) if c else 0)) if Zl else np.zeros(0)
    aZ = at + (I['BA'][0][Zl] @ muzc if Zl else 0.0)
    lo, hi = (aZ - I['kp'][0]) / (GAM * s), (aZ + I['km'][0]) / (GAM * s)
    xu = min(max(x0, lo), hi); xt = min(max(xu, 0), 2)
    # is x~_u in the incumbent's piece? (Z constant on the segment between x^- and x~_u)
    seg = np.linspace(x0, xu, 400); inpiece = all(G(I, np.array([y]))[1] == Z0 for y in seg[1:])
    clipped_same = (xu <= 0 and xA[0] <= 1e-5) or (xu >= 2 and xA[0] >= 2 - 1e-5)
    # direction: every status change drives an ETF to zero (Z grows) -> true trade shorter
    Zpath = [G(I, np.array([y]))[1] for y in seg]; grows = all(set(Zpath[i]) <= set(Zpath[i + 1]) for i in range(len(Zpath) - 1)) and Zpath[-1] != Z0
    shorter = abs(xA[0] - x0) < abs(xt - x0) - 1e-6
    return dict(dec_ok=dec_ok, inpiece=inpiece, eq=abs(xt - xA[0]) <= 1e-5, clipped_same=clipped_same, moved=abs(xu - x0) > 1e-9,
                grows=grows, shorter=shorter, miss=abs(xt - xA[0]), true=abs(xA[0] - x0))


def job_one_etf(k):
    rng = np.random.default_rng([4037, 2, k]); N = int(rng.integers(1, 4)); sd = rng.uniform(0.001, 0.01)
    I = dict(BA=np.ones((N, 1)), S=np.array([[0.08 ** 2 + sd ** 2]]), lam=np.array([rng.uniform(-0.01, 0.03)]), cE=np.array([rng.uniform(0, 0.002)]),
             a=rng.uniform(-0.01, 0.01, N), V=0.02 ** 2 * (1 + rng.uniform(0.01, 3, N)), kp=rng.uniform(0, 0.02, N), km=rng.uniform(0, 0.02, N),
             x0=rng.uniform(0, 0.25, N), cap=np.full(N, 0.25))
    xA, xE = solve(I); q = float(np.sum(xA)); muE = I['lam'][0] - I['cE'][0]
    atzero = xE[0] <= 1e-5; rule = muE <= GAM * I['S'][0, 0] * q
    edge = abs(muE - GAM * I['S'][0, 0] * q) < 1e-9
    return dict(ok=(atzero == rule) or edge, atzero=atzero)


def main():
    with Pool(9) as p:
        R = p.map(job_random, range(500), chunksize=10); Tg = p.map(job_targeted, range(500), chunksize=10); O = p.map(job_one_etf, range(300), chunksize=10)
    Rk = [r for r in R if not r['knife']]
    print(f"random draws: {len(R)} ({len(R) - len(Rk)} knife edges set aside); ETFs at zero: none {sum(r['nZ'] == 0 for r in Rk)}, one {sum(r['nZ'] == 1 for r in Rk)}, two {sum(r['nZ'] == 2 for r in Rk)}")
    print(f"part 1: fund lines with the slacks hold at {sum(r['ok1'] for r in Rk)}/{len(Rk)}")
    print(f"part 2: formula Z = solver's at-zero set at {sum(r['Zok'] for r in Rk)}/{len(Rk)}; |zeta_Z - (-g_Z)| max {max(r['zerr'] for r in Rk):.1e}; exactly one valid set at {sum(r['nf'] == 1 for r in Rk)}/{len(Rk)}")
    print(f"part 5(a) one ETF: at zero iff mu_E <= gamma sigma_EE q at {sum(o['ok'] for o in O)}/{len(O)} ({sum(o['atzero'] for o in O)} at zero)")
    print(f"part 3(a): hold test = no fund traded at {sum(r['hold'] for r in Rk)}/{len(Rk)} ({sum(r['nhold'] for r in Rk)} holds)")
    sh = [s for r in Rk for s in r['shifts']]
    print(f"part 3(d): {len(sh)} shifts at fixed Z: |dG - r_iZ' B^E_Z.c e| max {max(s[0] for s in sh):.1e}; formula's G vs solver's marginal max {max(s[1] for s in sh):.1e}; "
          f"zero when Z is empty at {sum(s[3] == 0 for s in sh if s[2])}/{sum(s[2] for s in sh)}")
    F = [r['fold'] for r in Rk if r['fold'] is not None]
    print(f"part 5(d) fold-in: {len(F)} instances with an ETF at zero; max holding difference {max(F):.1e}")
    print(f"part 3(c) one fund (targeted draws): decision from G(x^-) = solve at {sum(t['dec_ok'] for t in Tg)}/{len(Tg)}")
    inp = [t for t in Tg if t['inpiece']]; out = [t for t in Tg if not t['inpiece']]
    print(f"part 4 drop-Z: root in the incumbent's piece {len(inp)}: equal to the solve at {sum(t['eq'] for t in inp)}; outside {len(out)}: coincide when both clipped to the same bound "
          f"{sum(t['eq'] for t in out if t['clipped_same'])}/{sum(t['clipped_same'] for t in out)}, differ otherwise {sum(not t['eq'] for t in out if not t['clipped_same'])}/{sum(not t['clipped_same'] for t in out)}")
    gr = [t for t in out if t['grows'] and not t['clipped_same']]
    print(f"  every change drives an ETF to zero: true trade shorter at {sum(t['shorter'] for t in gr)}/{len(gr)}; median miss {np.median([t['miss'] for t in out if not t['clipped_same']]):.2f}, "
          f"median true trade {np.median([t['true'] for t in out if not t['clipped_same']]):.2f}")


if __name__ == "__main__":
    main()
