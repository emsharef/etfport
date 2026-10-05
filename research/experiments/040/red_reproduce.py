"""Red's reproduction of experiment 040 (claim 041), written without reading run.py or report.py.
Coordinates w = x^E + Q x^A (B^E = I_2, so Q = B^A'); x^E >= 0 <=> w >= Q x^A. All objectives are solved in bp (x 1e4)
with CLARABEL at tight tolerances. Draws follow the Design's ranges with red's own seeds."""
import sys, itertools, warnings
import numpy as np, cvxpy as cp
from multiprocessing import Pool
warnings.simplefilter('ignore')
GAM = 5.0; SF = np.diag([0.08 ** 2, 0.04 ** 2]); BP = 1e4
SOLV = dict(solver=cp.CLARABEL, tol_gap_abs=1e-12, tol_gap_rel=1e-12, tol_feas=1e-12, max_iter=500)


def GE(w, I): return I['mu'] @ w - GAM / 2 * w @ I['S'] @ w
def H(x, I): return I['a'] @ x - GAM / 2 * x @ (I['V'] * x) - I['kp'] @ np.maximum(x - I['x0'], 0) - I['km'] @ np.maximum(I['x0'] - x, 0)
def Hx(x, I): return I['a'] @ x - GAM / 2 * cp.sum(cp.multiply(I['V'], cp.square(x))) - I['kp'] @ cp.pos(x - I['x0']) - I['km'] @ cp.pos(I['x0'] - x)


def solve(I, kind, ws=None):
    N = len(I['a']); x = cp.Variable(N); w = cp.Variable(2); L = np.linalg.cholesky(I['S'])
    GEx = I['mu'] @ w - GAM / 2 * cp.sum_squares(L.T @ w)
    cons = [x >= 0, x <= I['xb']]
    if kind == 'joint': obj = GEx + Hx(x, I); cons.append(w >= I['Q'] @ x)
    elif kind == 'stage1': obj = GEx; cons.append(w >= I['Q'] @ x)
    elif kind == 'fibre': obj = Hx(x, I); cons.append(I['Q'] @ x <= ws + 1e-12); w = None
    elif kind == 'soft': obj = Hx(x, I) - GAM / 2 * cp.sum_squares(L.T @ (w - ws)); cons.append(w >= I['Q'] @ x)
    pr = cp.Problem(cp.Maximize(BP * obj), cons); pr.solve(**SOLV)
    return x.value, (w.value if w is not None else None), pr.value / BP


def VE(q, I):
    for k in range(3):
        for Z in itertools.combinations(range(2), k):
            Z = list(Z); c = [j for j in range(2) if j not in Z]; w = np.array(q, float)
            if c: w[c] = np.linalg.solve(GAM * I['S'][np.ix_(c, c)], I['mu'][c] - GAM * I['S'][np.ix_(c, Z)] @ q[Z])
            z = GAM * I['S'] @ w - I['mu']
            if np.all(w >= q - 1e-13) and np.all(z[Z] >= -1e-13): return GE(w, I)


def draw(rng, one):
    if one:
        B = np.array([[1, 0.5]]) if rng.random() < 0.5 else np.array([[1, -0.3]]); xb = rng.choice([0.25, 2.0])
    else:
        B = np.array([[1, 0.5], [1, 0.2], [1, -0.3]]); xb = rng.choice([0.25, 1.0])
    N = B.shape[0]; sd = rng.uniform(0.001, 0.01, 2)
    I = dict(S=SF + np.diag(sd ** 2), mu=rng.uniform(-0.01, 0.03, 2), Q=B.T.copy(), a=rng.uniform(-0.01, 0.01, N),
             V=0.02 ** 2 * (1 + rng.uniform(0.01, 3, N)), kp=rng.uniform(0, 0.02, N), km=rng.uniform(0, 0.02, N), xb=np.full(N, xb))
    I['x0'] = rng.uniform(0, 1, N) * xb
    return I


def band_ok(I, x2, zeta, tol=1e-9):
    G = I['a'] - GAM * I['V'] * x2 - I['Q'].T @ zeta; ok = True
    for i in range(len(x2)):
        up, dn = x2[i] > I['x0'][i] + 1e-7, x2[i] < I['x0'][i] - 1e-7
        atc, atz = x2[i] > I['xb'][i] - 1e-7, x2[i] < 1e-7
        if up: lo, hi = I['kp'][i], (np.inf if atc else I['kp'][i])
        elif dn: lo, hi = (-np.inf if atz else -I['km'][i]), -I['km'][i]
        else: lo, hi = (-np.inf if atz else -I['km'][i]), (np.inf if atc else I['kp'][i])
        ok &= lo - tol <= G[i] <= hi + tol
    return ok


def one(args):
    k, one_fund = args
    rng = np.random.default_rng([4040, int(one_fund), k]); I = draw(rng, one_fund); N = len(I['a'])
    xJ, wJ, J = solve(I, 'joint'); x1, ws, _ = solve(I, 'stage1'); x2 = solve(I, 'fibre', ws)[0]
    T = GE(ws, I) + H(x2, I); zeta = GAM * I['S'] @ ws - I['mu']
    out = dict(N=N, Lam=J - T, gapF=float(np.abs(x2 - xJ).max()), zmin=float(zeta.min()), compl=float(np.abs(zeta * (ws - I['Q'] @ x2)).max()),
               band=band_ok(I, x2, zeta), atzeroJ=bool(np.any(wJ - I['Q'] @ xJ < 1e-7)))
    if N == 1:
        r = I['Q'][:, 0]; lo = max([0.0] + [ws[j] / r[j] for j in range(2) if r[j] < 0]); hi = min([I['xb'][0]] + [ws[j] / r[j] for j in range(2) if r[j] > 0])
        c = GAM * I['V'][0]; bs = min(max(I['x0'][0], (I['a'][0] - I['kp'][0]) / c), (I['a'][0] + I['km'][0]) / c)
        out.update(x2err=abs(x2[0] - min(max(bs, lo), hi)), inint=lo - 1e-7 <= xJ[0] <= hi + 1e-7,
                   misfit=VE(r * x2[0], I) - GE(ws, I), x1in=lo - 1e-9 <= x1[0] <= hi + 1e-9)
    # 3(a): soft with unconstrained stage 1
    wTB = np.linalg.solve(GAM * I['S'], I['mu']); xa, wa, _ = solve(I, 'soft', wTB); out['Lsa'] = J - (GE(wa, I) + H(xa, I))
    # 3(b): soft with stage 1 over W_F (w_s = w*)
    xb2, wb2, T2 = solve(I, 'soft', ws); Ls = J - (GE(wb2, I) + H(xb2, I)); nu = I['mu'] - GAM * I['S'] @ ws
    x = cp.Variable(N); pr = cp.Problem(cp.Minimize(0), [I['Q'] @ x <= wTB, x >= 0, x <= I['xb']]); pr.solve(solver=cp.CLARABEL); reach = pr.status == 'optimal'
    # normal cone of W_F = Q(box) + R^2_+ at w*: nu <= 0 and max_x nu' Q x over the box <= nu' w*
    qn = I['Q'].T @ nu; nc = bool(np.all(nu <= 1e-9) and (np.sum(np.maximum(qn, 0) * I['xb']) <= nu @ ws + 1e-9))
    gap = max(float(np.abs(xb2 - xJ).max()), float(np.abs(wb2 - wJ).max()))
    L = np.linalg.cholesky(I['S']); tilt = lambda xx, ww: H(xx, I) - GAM / 2 * (ww - ws) @ I['S'] @ (ww - ws)
    solves_tilted = tilt(xJ, wJ) >= tilt(xb2, wb2) - 1e-10
    out.update(Ls=Ls, reach=reach, nc=nc, nu0=float(np.abs(nu).max()), gap=gap, bound=nu @ (wJ - wb2) - Ls, solves_tilted=solves_tilted,
               fund_same=float(np.abs(xb2 - xJ).max()), w_diff=float(np.abs(wb2 - wJ).max()))
    return out


def main():
    jobs = [(k, False) for k in range(500)] + [(k, True) for k in range(500)]
    with Pool(9) as p: R = p.map(one, jobs, chunksize=10)
    print(f"{len(R)} draws; ETF at zero at the joint optimum in {sum(r['atzeroJ'] for r in R)}")
    ex = [r for r in R if r['gapF'] <= 1e-5]
    print(f"part 1: min zeta* {min(r['zmin'] for r in R):.1e}, max complementarity {max(r['compl'] for r in R):.1e}; band test = exactness (holdings, 1e-5) at "
          f"{sum(r['band'] == (r['gapF'] <= 1e-5) for r in R)}/{len(R)} ({len(ex)} exact)")
    O = [r for r in R if r['N'] == 1]
    print(f"part 2: x_2 vs clipped band max {max(r['x2err'] for r in O):.1e}; x_1 in interval {sum(r['x1in'] for r in O)}/{len(O)}; "
          f"T = J iff x_J in interval {sum(r['inint'] == (r['gapF'] <= 1e-5) for r in O)}/{len(O)}; misfit max {max(abs(r['misfit']) for r in O):.1e}")
    print(f"part 3(a): max Lambda_s {max(r['Lsa'] for r in R):.1e}")
    Rr = [r for r in R if r['reach']]; Ru = [r for r in R if not r['reach']]
    print(f"part 3(b): reachable {len(Rr)}: max |Lambda_s| {max(abs(r['Ls']) for r in Rr):.1e}, max gap {max(r['gap'] for r in Rr):.1e}; normal cone {sum(r['nc'] for r in R)}/{len(R)}; "
          f"nonzero nu at unreachable {sum(r['nu0'] > 1e-9 for r in Ru)}/{len(Ru)}")
    gaps = np.array([r['gap'] for r in Ru]); exact = gaps <= 1e-4
    print(f"  unreachable {len(Ru)}: bound holds at {sum(r['Ls'] >= -1e-10 and r['bound'] >= -1e-10 for r in Ru)}; exact (gap <= 1e-4) {exact.sum()}, inexact {(~exact).sum()}; "
          f"largest exact gap {gaps[exact].max():.1e}, smallest inexact gap {gaps[~exact].min():.1e}")
    print(f"  iff: 'joint optimum solves the tilted stage 2' = exact at {sum(r['solves_tilted'] == (r['gap'] <= 1e-4) for r in Ru)}/{len(Ru)}; "
          f"loss ranges: exact up to {max(r['Ls'] for r, e in zip(Ru, exact) if e):.1e}, inexact from {min(r['Ls'] for r, e in zip(Ru, exact) if not e):.1e}")
    fs = [r for r, e in zip(Ru, exact) if not e and r['fund_same'] <= 1e-6]
    print(f"  inexact draws with the fund holdings equal to the joint's: {len(fs)} (min w difference {min(r['w_diff'] for r in fs) if fs else float('nan'):.1e})")


if __name__ == "__main__":
    main()
