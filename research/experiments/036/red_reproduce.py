"""Red's reproduction of experiment 036 (claim 107), written without reading run.py, report.py or fastdp.py.

Exact two-instrument DP (fund A, ETF E) in deviation coordinates d = x - x*: with Sigma fixed, beta = 1, no marking and
no bound binding, V_t(d^-) = min_d [ C_A + C_E + (gamma/2) d' Sigma d + E V_{t+1}(d - eps) ], eps the targets' four-point
step (an exact index shift on a grid whose steps divide the target steps). The trading cost is separable, so the
minimization is two exact directional L1 transforms, one per axis. Reported error: the fund-edge resolution
h_A + |Sigma_AE| gamma h_E / c^res (the ETF step reaches the fund's edge through the hedge ratio).
"""
import numpy as np
from multiprocessing import Pool

GAM = 5.0; SEE = 0.0854 ** 2; SAA = 0.0854 ** 2 + 0.02 ** 2; T = 8; CAP = 1500


def l1min(W, kp, km, h, axis):
    """V(x^-) = min_y W(y) + kp (y - x^-)^+ + km (x^- - y)^+ along an axis of step h (exact on the grid)."""
    n = W.shape[axis]; s = np.arange(n).reshape([-1 if a == axis else 1 for a in range(W.ndim)]) * h
    buy = np.flip(np.minimum.accumulate(np.flip(W + kp * s, axis), axis=axis), axis) - kp * s
    sell = np.minimum.accumulate(W - km * s, axis=axis) + km * s
    return np.minimum(buy, sell)


def shift(V, i, j):
    """V(d - eps) for eps = (i, j) grid steps, edge-clamped."""
    out = np.roll(V, (i, j), axis=(0, 1))
    if i > 0: out[:i, :] = out[i:i + 1, :]
    if i < 0: out[i:, :] = out[i - 1:i, :]
    if j > 0: out[:, :j] = out[:, j:j + 1]
    if j < 0: out[:, j:] = out[:, j - 1:j]
    return out


def cell(args):
    corr, kAp, kAm, kEp, kEm, r, step = args
    SAE = corr * np.sqrt(SAA * SEE); S = np.array([[SAA, SAE], [SAE, SEE]]); rho = SAE / SEE
    cres = GAM * (SAA - SAE ** 2 / SEE); ceil = (kAp + kAm) / cres; alone = (kAp + kAm) / (GAM * SAA)
    wA = ceil; wE = (kEp + kEm) / (GAM * SEE) if kEp + kEm > 0 else 0.002 / (GAM * SEE)
    uA, uE = step * wA, step * wE
    # widened parallelotope (beta = 1): (gamma S)^{-1} prod [-(k+ + k-), k- + k+]
    Si = np.linalg.inv(GAM * S); vt = np.array([[sa * (kAp + kAm), se * (kEp + kEm)] for sa in (-1, 1) for se in (-1, 1)])
    ext = np.abs(vt @ Si.T).max(0) * 1.2 + np.array([uA, uE]) * 2
    ext = np.maximum(ext, np.array([2 * ceil, 3 * wE]))
    mA = max(1, int(round(50 if step == 0.5 else 10))); mE = mA
    hA, hE = uA / mA, uE / mE
    while 2 * ext[0] / hA > CAP:
        if mA > 1: mA = max(1, mA // 2); hA = uA / mA
        else: ext[0] = CAP * hA / 2
    while 2 * ext[1] / hE > CAP:
        if mE > 1: mE = max(1, mE // 2); hE = uE / mE
        else: ext[1] = CAP * hE / 2
    nA = int(2 * ext[0] / hA) + 1; nE = int(2 * ext[1] / hE) + 1
    a = (np.arange(nA) - nA // 2) * hA; e = (np.arange(nE) - nE // 2) * hE
    D1, D2 = np.meshgrid(a, e, indexing='ij')
    Q = GAM / 2 * (S[0, 0] * D1 ** 2 + 2 * S[0, 1] * D1 * D2 + S[1, 1] * D2 ** 2)
    law = [((mA, mE), (1 + r) / 4), ((-mA, -mE), (1 + r) / 4), ((mA, -mE), (1 - r) / 4), ((-mA, mE), (1 - r) / 4)]
    tolA = hA + abs(SAE) * GAM * hE / cres
    Vn = None; res = []
    pe_idx = np.unique(np.round(np.linspace(-0.45, 0.45, 41) * 2 * (np.abs(vt @ Si.T).max(0)[1]) / hE).astype(int) + nE // 2)
    pe_idx = pe_idx[(pe_idx > 5) & (pe_idx < nE - 6)]
    for t in reversed(range(T)):
        W = Q.copy()
        if Vn is not None:
            W += sum(p * shift(Vn, i, j) for (i, j), p in law)
        U = l1min(W, kEp, kEm, hE, 1)            # ETF-optimized value U(a; p^-), p^- along axis 1
        V = l1min(U, kAp, kAm, hA, 0)
        hold = U - V <= 1e-15          # held iff staying is optimal (V <= U always)
        nt = W - V <= 1e-15
        rows = []
        for j in pe_idx:
            col = np.where(hold[:, j])[0]
            if len(col) == 0 or col[0] < 3 or col[-1] > nA - 4: continue
            contiguous = col[-1] - col[0] + 1 == len(col)
            lo, hi = a[col[0]], a[col[-1]]
            info = dict(j=j, lo=lo, hi=hi, contig=contiguous)
            # ETF optimizer at the fund's edges: its trade direction, and whether it sits at the grid's edge (a bound)
            info['etf_edge'] = False
            for nm, ia in (('hi', col[-1]), ('lo', col[0])):
                obj = W[ia, :] + np.where(e > e[j], kEp * (e - e[j]), kEm * (e[j] - e))
                k = int(np.argmin(obj)); info[nm + '_dir'] = 1 if k > j else (-1 if k < j else 0)
                info['etf_edge'] |= (k < 3) or (k > nE - 4)
            rows.append(info)
        # no-trade region checks (part 2)
        pts = np.argwhere(nt); inside = 0; diam = 0.0
        if len(pts):
            X = np.column_stack([a[pts[:, 0]], e[pts[:, 1]]])
            edge = (pts[:, 0] < 3) | (pts[:, 0] > nA - 4) | (pts[:, 1] < 3) | (pts[:, 1] > nE - 4)
            X = X[~edge]
            if len(X):
                y = X @ (GAM * S)          # (gamma S) d must lie in prod [-(k+ + k-), k- + k+] (beta = 1), per coordinate
                lim = np.array([[-(kAp + kAm), kAm + kAp], [-(kEp + kEm), kEm + kEp]])
                slackA = GAM * np.abs(S[0]) @ np.array([hA, hE]); slackE = GAM * np.abs(S[1]) @ np.array([hA, hE])
                inside = int(np.sum((y[:, 0] < lim[0, 0] - slackA) | (y[:, 0] > lim[0, 1] + slackA) | (y[:, 1] < lim[1, 0] - slackE) | (y[:, 1] > lim[1, 1] + slackE)))
                rng = np.random.default_rng(t); I = rng.integers(0, len(X), (20000, 2))
                dx = X[I[:, 0]] - X[I[:, 1]]; lhs = GAM * np.einsum('ij,jk,ik->i', dx, S, dx)
                rhs = (kAp + kAm) * np.abs(dx[:, 0]) + (kEp + kEm) * np.abs(dx[:, 1])
                slack = (kAp + kAm) * hA + (kEp + kEm) * hE + GAM * (np.abs(dx) @ np.abs(S) @ np.array([hA, hE])) * 2
                diam = float(np.max((lhs - rhs - slack) / np.maximum(rhs, 1e-18)))
        res.append(dict(t=t, rows=rows, nt_out=inside, diam=diam))
        Vn = V
    # part 3: reduced one-instrument DP with curvature c^res, fund target lattice (+-uA, prob 1/2)
    red = None
    if kEp + kEm == 0:
        n1 = int(2 * max(3 * ceil, 2 * uA) / hA) + 1; x = (np.arange(n1) - n1 // 2) * hA; Vr = None; red = {}
        for t in reversed(range(T)):
            Wr = cres / 2 * x ** 2
            if Vr is not None:
                Wr = Wr + 0.5 * (shift(Vr[:, None], mA, 0)[:, 0] + shift(Vr[:, None], -mA, 0)[:, 0])
            Vr1 = l1min(Wr[:, None], kAp, kAm, hA, 0)[:, 0]; hl = np.where(Wr - Vr1 <= 1e-15)[0]
            red[t] = (x[hl[0]], x[hl[-1]]); Vr = Vr1
    H_p = abs(rho) * (kEp + kEm) if rho >= 0 else abs(rho) * (kEm + kEp)
    return dict(args=args, rho=rho, cres=cres, ceil=ceil, alone=alone, tolA=tolA, hA=hA, hE=hE, nA=nA, nE=nE, res=res, red=red,
                br_hi=(kAm + kAp + H_p) / cres, br_lo=-(kAp + kAm + H_p) / cres)


def cells():
    C = []
    for corr in [0, 0.5, 0.9, 0.97]:
        for r in [-0.8, 0, 0.8]:
            for step in [0.5, 0.1]:
                for kA in [0.001, 0.005]:
                    for kE in [0, 0.0002, 0.001, 0.005]:
                        C.append((corr, kA, kA, kE, kE, r, step))
                C.append((corr, 0.01, 0.0, 0.0005, 0.0005, r, step))
    return C


def main():
    C = cells()
    with Pool(6) as pool: out = pool.map(cell, C, chunksize=1)
    nb = ceil_bad = br_bad = noncontig = etf_edge = 0; maxratio = 0; ntout = 0; dbad = 0
    d_edge = []; d_width = {'opp': [], 'idle': [], 'same': [], 'mixed': 0}; last_between = 0
    p3 = []; p3_range = 0; table = {}
    for o in out:
        corr, kAp, kAm, kEp, kEm, r, step = o['args']
        for R in o['res']:
            ntout += R['nt_out']; dbad += R['diam'] > 1e-9
            widths = []
            for w in R['rows']:
                if not w['contig']: noncontig += 1; continue
                if w['etf_edge']: etf_edge += 1; continue
                nb += 1; wd = w['hi'] - w['lo']; widths.append(wd)
                maxratio = max(maxratio, wd / o['ceil']); ceil_bad += wd > o['ceil'] + o['tolA']
                br_bad += (w['hi'] > o['br_hi'] + o['tolA']) or (w['lo'] < o['br_lo'] - o['tolA'])
                if R['t'] == T - 1 and kEp + kEm > 0:
                    last_between += not (o['alone'] - 2 * o['tolA'] <= wd <= o['ceil'] + 2 * o['tolA'])
                    dh, dl = w['hi_dir'], w['lo_dir']
                    for nm, dd in (('hi', dh), ('lo', dl)):
                        if dd != 0:
                            cE = kEp if dd > 0 else -kEm
                            f = (kAm + o['rho'] * cE) / o['cres'] if nm == 'hi' else -(kAp - o['rho'] * cE) / o['cres']
                            d_edge.append(abs(w[nm] - f) / o['tolA'])
                    if dh == -1 and dl == 1: d_width['opp'].append(abs(wd - (kAp + kAm - abs(o['rho']) * (kEp + kEm)) / o['cres']) / o['tolA'])
                    elif dh == 0 and dl == 0: d_width['idle'].append(abs(wd - o['alone']) / o['tolA'])
                    elif dh == dl: d_width['same'].append(abs(wd - o['ceil']) / o['tolA'])
                    else: d_width['mixed'] += 1
            if R['t'] == 0 and kEp == 0.001 and kAp == kAm:
                table[(corr, kAp, step, r)] = np.median(widths) / o['ceil'] if widths else np.nan
        if o['red'] is not None:
            for R in o['res']:
                lo_r, hi_r = o['red'][R['t']]; ws = [(w['lo'], w['hi']) for w in R['rows'] if w['contig']]
                if ws:
                    p3.append(max(max(abs(l - lo_r), abs(h - hi_r)) for l, h in ws) / o['hA'])
                    p3_range = max(p3_range, (max(h for _, h in ws) - min(h for _, h in ws)) / o['hA'])
    print(f"{len(out)} cells, {T} reviews: {nb} contiguous fund bands away from grid edges ({noncontig} non-contiguous and {etf_edge} with the ETF optimizer at the grid's edge, a binding bound, set aside)")
    print(f"part 1b: width > ceiling + resolution at {ceil_bad}; largest width/ceiling {maxratio:.4f}")
    print(f"part 1c: edges outside the bracket (beyond resolution) {br_bad}")
    print(f"part 1d (t = T-1): edge vs formula where the ETF trades: {len(d_edge)} edges, max {max(d_edge):.2f} resolutions; widths: opposite {len(d_width['opp'])} (max {max(d_width['opp']) if d_width['opp'] else 0:.2f}), "
          f"idle {len(d_width['idle'])} (max {max(d_width['idle']) if d_width['idle'] else 0:.2f}), same {len(d_width['same'])} (max {max(d_width['same']) if d_width['same'] else 0:.2f}), mixed {d_width['mixed']}; "
          f"width outside [fund-alone, ceiling] beyond 2 resolutions: {last_between}")
    print(f"part 2: no-trade grid points outside the widened parallelotope (beyond one step) {ntout}; diameter-inequality violations {dbad}")
    print(f"part 3 (kappa_E = 0): {len(p3)} (cell, review) pairs, max |band - reduced band| {max(p3):.2f} fund steps; band range across ETF incumbents {p3_range:.2f} fund steps")
    print("open item, median width/ceiling at t = 0 (T = 8, ETF 10 bp):")
    for corr in [0.97, 0.5]:
        for kA, st in [(0.001, 0.5), (0.001, 0.1), (0.005, 0.5)]:
            print(f"  corr {corr}, fund {kA*1e4:.0f} bp, step {st}: " + ", ".join(f"r {r:+.1f}: {table[(corr, kA, st, r)]:.2f}" for r in [-0.8, 0, 0.8]))


if __name__ == "__main__":
    main()
