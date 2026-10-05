"""Red's reproduction of experiment 032 (claim 106), written without reading run.py, report.py or checks/106.

One review of claim 104's setting, solved with cvxpy/CLARABEL (objective in bp), for the three action
classes F, E^- (x^A <= x^{A-}) and E^0 (x^A = x^{A-}). The formula side is coded from claim 106's text.
Instance: the Design's, with Deviation 1 (B^E = I_2) and Deviation 2's open points.
"""
import sys, warnings
import numpy as np, cvxpy as cp
warnings.simplefilter('ignore')
from multiprocessing import Pool

GAM = 5.0; SF = np.diag([0.08 ** 2, 0.04 ** 2]); PL = np.diag([0.005 ** 2] * 2); LAM = np.array([0.015, 0.005])
BA = np.array([[1, 0.5], [1, 0.2], [1, -0.3]]); V = np.full(3, 0.02 ** 2 + 0.0035 ** 2); H0 = 1.0
BP = 1e4


class Prob:
    def __init__(self, BE, BAm, cls):
        M = BE.shape[0]; self.M = M
        self.ah = cp.Parameter(3); self.x0 = cp.Parameter(3, nonneg=True); self.cap = cp.Parameter(3, nonneg=True)
        self.kA = cp.Parameter(3, nonneg=True); self.lam = cp.Parameter(2); self.L = cp.Parameter((2, 2))
        self.kE = cp.Parameter(M, nonneg=True); self.cE = cp.Parameter(M); self.xE0 = cp.Parameter(M)
        self.xA = cp.Variable(3); self.xE = cp.Variable(M)
        b = BAm.T @ self.xA + BE.T @ self.xE
        cost = self.kA @ cp.abs(self.xA - self.x0) + self.kE @ cp.abs(self.xE - self.xE0)
        Q = self.lam @ b - GAM / 2 * cp.sum_squares(self.L.T @ b) + self.ah @ self.xA - self.cE @ self.xE \
            - GAM / 2 * cp.sum(cp.multiply(V, cp.square(self.xA))) - cost
        self.cash = H0 - cp.sum(self.xA - self.x0) - cp.sum(self.xE - self.xE0) - cost
        cons = [self.xA >= 0, self.xA <= self.cap, self.xE >= 0, self.xE <= 1, self.cash >= 0]
        if cls == 'E-': cons.append(self.xA <= self.x0)
        if cls == 'E0': cons.append(self.xA == self.x0)
        self.pr = cp.Problem(cp.Maximize(BP * Q), cons)

    def solve(self, d):
        for k in ['ah', 'x0', 'cap', 'kA', 'lam', 'L', 'kE', 'cE', 'xE0']: getattr(self, k).value = d[k]
        self.pr.solve(solver=cp.CLARABEL, tol_gap_abs=1e-12, tol_gap_rel=1e-12, tol_feas=1e-12, max_iter=500)
        return self.pr.value / BP, self.xA.value.copy(), self.xE.value.copy(), float(self.cash.value)


MENU = {'span': np.eye(2), 'unreach': np.array([[1.0, 0.0]])}
BAS = {'span': BA, 'unreach': np.array([[1, 0.5], [1, 0.0], [1, 0.0]])}   # Deviation 2: funds 2-3 load (1, 0) on the unreachable menu
PROBS = {}


def probs(menu):
    if menu not in PROBS: PROBS[menu] = {c: Prob(MENU[menu], BAS[menu], c) for c in ['F', 'E-', 'E0']}
    return PROBS[menu]


def etf_incumbents(BE, BAm, lam, Sft, x0):
    bstar = np.linalg.solve(GAM * Sft, lam)
    return np.clip(np.linalg.lstsq(BE.T, bstar - BAm.T @ x0, rcond=None)[0], 0, 1)


def point(d):
    """d: menu, ah, x0, cap, kA, lam, Pl, kE, cE. Returns solves and hypothesis flag."""
    Sft = SF + d['Pl']; BE = MENU[d['menu']]; M = BE.shape[0]
    dd = dict(ah=d['ah'], x0=d['x0'], cap=d['cap'], kA=d['kA'], lam=d['lam'], L=np.linalg.cholesky(Sft),
              kE=d.get('kE', np.zeros(M)), cE=d.get('cE', np.zeros(M)), xE0=etf_incumbents(BE, BAS[d['menu']], d['lam'], Sft, d['x0']))
    out = {}; hyp = True
    for c, p in probs(d['menu']).items():
        J, xA, xE, cash = p.solve(dd); out[c] = (J, xA)
        hyp &= bool(np.all(xE > 1e-5) and np.all(xE < 1 - 1e-5) and cash > 1e-7)
    return out, hyp, dd['xE0']


# ---------- claim 106 formulas ----------
def psi(a, ah, v, kp, km, x0): return ah * a - GAM / 2 * v * a * a - kp * max(a - x0, 0) - km * max(x0 - a, 0)


def part2_terms(ah, v, kp, km, x0, cap):
    lo = (ah - kp) / (GAM * v); hi = (ah + km) / (GAM * v); p = ah - kp - GAM * v * x0; s = GAM * v * x0 - ah - km
    Cm = ((p * p / (2 * GAM * v)) if lo <= cap else psi(cap, ah, v, kp, km, x0) - psi(x0, ah, v, kp, km, x0)) if p > 0 else 0.0
    Sv = ((s * s / (2 * GAM * v)) if hi >= 0 else psi(0, ah, v, kp, km, x0) - psi(x0, ah, v, kp, km, x0)) if s > 0 else 0.0
    return Cm, Sv, p


def gfun(m, d, v):
    if m <= 0: return 0.0
    return m * m / (2 * GAM * v) if m <= GAM * v * d else m * d - GAM * v / 2 * d * d


def reduced(i, lam, Sft, BE):
    K = 2; PiR = BE.T @ np.linalg.pinv(BE @ BE.T) @ BE; PiU = np.eye(K) - PiR
    RR = PiR @ Sft @ PiR; RU = PiR @ Sft @ PiU; UU = PiU @ Sft @ PiU; RRi = np.linalg.pinv(RR)
    Jm = PiU - PiR @ RRi @ RU; SUR = UU - RU.T @ RRi @ RU
    Bi = BAS['unreach'][i]
    return float(Bi @ Jm.T @ lam), float(Bi @ SUR @ Bi)


def formula(d):
    Sft = SF + d['Pl']; BE = MENU[d['menu']]; Cm = Sv = 0.0; ps = []; ss = []
    for i in range(3):
        ah, v = d['ah'][i], V[i]
        if d['menu'] == 'unreach' and i == 0:
            da, dv = reduced(0, d['lam'], Sft, BE); ah += da; v += dv
        c, s, p = part2_terms(ah, v, d['kA'][i], d['kA'][i], d['x0'][i], d['cap'][i]); Cm += c; Sv += s; ps.append(p)
        ss.append(GAM * v * d['x0'][i] - ah - d['kA'][i])
    return Cm, Sv, ps, ss


def brackets(d):
    kE = d['kE']; cE = d['cE']; lbC = ubC = lbS = ubS = 0.0
    for i in range(3):
        r = BA[i]  # R = (B^E)^{-1} = I
        hp = float(np.sum(np.abs(r) * kE)); hm = hp  # symmetric ETF rates: selling r^+ and buying r^- cost the same either way
        A0 = d['ah'][i] + r @ cE - GAM * V[i] * d['x0'][i]; kp = km = d['kA'][i]; room_b = d['cap'][i] - d['x0'][i]; room_s = d['x0'][i]
        lbC += gfun(A0 - kp - hp, room_b, V[i]); ubC += gfun(A0 - kp + hm, room_b, V[i])
        lbS += gfun(-A0 - km - hm, room_s, V[i]); ubS += gfun(-A0 - km + hp, room_s, V[i])
    return lbC, ubC, lbS, ubS


def base(**kw):
    d = dict(menu='span', ah=np.array([0.0, 0.0, 0.0]), x0=np.array([0.0, 0.05, 0.05]), cap=np.full(3, 0.25),
             kA=np.full(3, 0.002), lam=LAM.copy(), Pl=PL.copy(), kE=np.zeros(2), cE=np.zeros(2))
    d.update(kw); return d


def with1(d, **kw):
    for k, v in kw.items():
        a = d[k].copy(); a[0] = v; d[k] = a
    return d


def run(job):
    tag, d = job
    out, hyp, _ = point(d)
    J, xJ = out['F']; Jm, _ = out['E-']; J0, _ = out['E0']
    st = sum(p.pr.status != 'optimal' for p in probs(d['menu']).values())
    return tag, d, J, Jm, J0, xJ, hyp, st


def jobs():
    J = []
    for cap in [0.25, 1.0]:
        for x in [0, 0.1, 0.2]:
            for a in np.linspace(-0.01, 0.03, 201): J.append(('c1', with1(base(), ah=a, x0=x, cap=cap)))
    for a in [0.002, 0.005, 0.01]:
        for x in np.linspace(0, 0.25, 101): J.append(('c2', with1(base(), ah=a, x0=x)))
    rng = np.random.default_rng([2032, 0])
    for _ in range(200):
        lam = rng.uniform(-0.01, 0.04, 2); Pl = np.diag(rng.uniform(0.001, 0.01, 2) ** 2)
        for _ in range(3):
            cap = rng.choice([0.1, 0.25, 1.0], 3); x0 = rng.uniform(0, 1, 3) * cap
            J.append(('c3', base(ah=rng.uniform(-0.01, 0.01, 3), kA=rng.uniform(0, 0.02, 3), cap=cap, x0=x0, lam=lam, Pl=Pl)))
    for a in [-0.005, -0.0019, 0.0]:
        for x in np.linspace(0, 0.25, 101): J.append(('c4', with1(base(), ah=a, x0=x)))
    for l2 in [-0.01, 0.005, 0.02]:
        for cap in [0.25, 1.0]:
            for x in [0, 0.1, 0.2]:
                for a in np.linspace(-0.01, 0.03, 201):
                    d = with1(base(menu='unreach', lam=np.array([0.015, l2]), kE=np.zeros(1), cE=np.zeros(1)), ah=a, x0=x, cap=cap); J.append(('c5', d))
    for kE in [0, 5e-4, 1e-3, 2.5e-3, 5e-3]:
        for fee in [0, 5e-4, 1e-3]:
            for a in np.linspace(-0.01, 0.03, 201):
                J.append(('c6', with1(base(kE=np.full(2, kE), cE=np.full(2, fee)), ah=a, x0=0.1)))
    return J


def main():
    J = jobs()
    with Pool(9) as pool: R = pool.map(run, J, chunksize=40)
    tol = 1e-11; stats = {}
    zero_bad = zero_n = 0; knife = 0
    for tag, d, Jf, Jm, J0, xJ, hyp, st in R:
        s = stats.setdefault(tag, dict(n=0, hyp=0, errC=0.0, errS=0.0, maxC=0.0, maxS=0.0, br_bad=0, pos=[], hyp_cap=[], out_dev=0.0, bought_from={}))
        s['n'] += 1
        if not hyp: s['hyp_cap'].append(d['cap'][0]);
        C, S = Jf - Jm, Jm - J0
        if tag == 'c3' and not hyp:
            s['out_dev'] = max(s['out_dev'], abs(C - formula(d)[0])); continue
        s['inacc'] = s.get('inacc', 0) + (st != 0)
        if not hyp: continue
        s['hyp'] += 1; s['maxC'] = max(s['maxC'], C); s['maxS'] = max(s['maxS'], S)
        if tag != 'c6':
            fC, fS, ps, _ = formula(d); s['errC'] = max(s['errC'], abs(C - fC)); s['errS'] = max(s['errS'], abs(S - fS))
            if tag == 'c5' and d['x0'][0] == 0 and C > tol:
                key = (d['lam'][1], d['cap'][0]); s['bought_from'][key] = min(s['bought_from'].get(key, 9), d['ah'][0])
        else:
            lbC, ubC, lbS, ubS = brackets(d)
            s['br_bad'] += not (lbC - 1e-10 <= C <= ubC + 1e-10 and lbS - 1e-10 <= S <= ubS + 1e-10)
            if ubC - lbC > 1e-9 and C > 1e-9: s['pos'].append(((d['kE'][0], d['cE'][0]), (C - lbC) / (ubC - lbC)))
            if d['kE'][0] == 0 and abs(d['ah'][0] - 0.03) < 1e-12: s.setdefault('c_top', {})[d['cE'][0]] = C
        # part 1a (off knife edges: fund purchase or sale excess within 1e-9 of zero)
        # (the excesses in the claim's own moments: reduced for fund 1 on the unreachable menu)
        _, _, pe, se = formula(d)
        if min(abs(np.array(pe + se))) < 1e-9: knife += 1; continue
        bought = bool(np.any(xJ > d['x0'] + 1e-7)); traded = bool(np.any(np.abs(xJ - d['x0']) > 1e-7))
        zero_n += 1; zero_bad += ((abs(C) < tol) == bought) + ((abs(Jf - J0) < tol) == traded)
    for tag in ['c1', 'c2', 'c3', 'c4', 'c5', 'c6']:
        s = stats[tag]; caps = sorted(set(np.round(s['hyp_cap'], 3)))
        line = f"{tag}: {s['hyp']} of {s['n']} meet hypotheses (excluded fund-1 caps {caps}); max C^- {s['maxC'] * BP:.2f} bp, max J^- - J^0 {s['maxS'] * BP:.2f} bp"
        line += f"; solves not 'optimal' (in hypotheses) {s.get('inacc', 0)}"
        if tag != 'c6': line += f"; |C - formula| {s['errC']:.1g}, |J^- - J^0 - formula| {s['errS']:.1g}"
        if tag == 'c3': line += f"; outside hypotheses C^- departs from the formula by up to {s['out_dev'] * BP:.1f} bp"
        if tag == 'c5': line += "; bought from x^-=0 at alpha_hat_1 >= " + ", ".join(f"{k}: {v * 100:.2f}%" for k, v in sorted(s['bought_from'].items()))
        if tag == 'c6':
            pos = {}
            for k, p in s['pos']: pos.setdefault(k, []).append(p)
            meds = [np.median(v) for v in pos.values()]; mx = max(max(v) for v in pos.values())
            line += f"; bracket violations {s['br_bad']}; position of C^- in bracket: medians {min(meds):.2f}-{max(meds):.2f}, max {mx:.2f}; C^- at alpha 3%, zero ETF rate, by fee: " + \
                ", ".join(f"{f * 100:.2f}%: {c * BP:.1f} bp" for f, c in sorted(s['c_top'].items()))
        print(line)
    print(f"part 1a: {zero_n} points off knife edges ({knife} set aside), mismatches {zero_bad}")
    # named equity-style illustration (curve 4)
    for a, x in [(-0.0019, 0.25), (-0.005, 0.25)]:
        out, hyp, _ = point(with1(base(), ah=a, x0=x)); print(f"curve 4 alpha {a * 100:.2f}%, x^- {x}: J^- - J^0 = {(out['E-'][0] - out['E0'][0]) * BP:.2f} bp, C^- = {(out['F'][0] - out['E-'][0]) * BP:.2g} bp (hyp {hyp})")


if __name__ == "__main__":
    main()
