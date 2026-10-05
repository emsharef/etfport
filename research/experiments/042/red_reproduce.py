"""Red's reproduction of experiment 042 (claim 108 parts 1-2), written without reading run.py or report.py.
Red's own exact two-instrument DP (its experiment 036 reproduction's transforms and grid rule; argument 1 is the directory
holding that red_reproduce.py), measured at every usable ETF column and fund row. Held sets are read two ways: with a tie
tolerance 1e-12 max|W| (Deviation 1) and with strict equality."""
import sys; sys.path.insert(0, sys.argv[1])
import numpy as np
from multiprocessing import Pool
import red_reproduce as R36
from red_reproduce import l1min, shift
GAM, SAA, SEE, T, CAP = R36.GAM, R36.SAA, R36.SEE, R36.T, R36.CAP


def grid(args):
    corr, kAp, kAm, kEp, kEm, r, step = args
    SAE = corr * np.sqrt(SAA * SEE); S = np.array([[SAA, SAE], [SAE, SEE]]); cres = GAM * (SAA - SAE ** 2 / SEE)
    wA = (kAp + kAm) / cres; wE = (kEp + kEm) / (GAM * SEE) if kEp + kEm > 0 else 0.002 / (GAM * SEE)
    uA, uE = step * wA, step * wE
    Si = np.linalg.inv(GAM * S); vt = np.array([[sa * (kAp + kAm), se * (kEp + kEm)] for sa in (-1, 1) for se in (-1, 1)])
    ext = np.abs(vt @ Si.T).max(0) * 1.2 + np.array([uA, uE]) * 2 + 3 * np.array([uA, uE])
    ext = np.maximum(ext, np.array([2 * wA, 3 * wE]) + 3 * np.array([uA, uE]))
    mA = mE = 50 if step == 0.5 else 10; hA, hE = uA / mA, uE / mE
    while 2 * ext[0] / hA > CAP:
        if mA > 1: mA = max(1, mA // 2); hA = uA / mA
        else: ext[0] = CAP * hA / 2
    while 2 * ext[1] / hE > CAP:
        if mE > 1: mE = max(1, mE // 2); hE = uE / mE
        else: ext[1] = CAP * hE / 2
    nA, nE = int(2 * ext[0] / hA) + 1, int(2 * ext[1] / hE) + 1
    return S, SAE, cres, hA, hE, mA, mE, nA, nE


def bands(mask, axis):
    """edges of the held set along axis for every line; None if empty or non-contiguous."""
    m = mask if axis == 0 else mask.T; n = m.shape[0]; out = []
    idx = np.arange(n)[:, None]
    anyh = m.any(0); first = np.argmax(m, 0); last = n - 1 - np.argmax(m[::-1], 0); cnt = m.sum(0)
    contig = anyh & (cnt == last - first + 1)
    return first, last, contig


def cell(args):
    corr, kAp, kAm, kEp, kEm, r, step = args
    S, SAE, cres, hA, hE, mA, mE, nA, nE = grid(args)
    rho, rhoA = SAE / SEE, SAE / SAA; cresE = GAM * (SEE - SAE ** 2 / SAA)
    a = (np.arange(nA) - nA // 2) * hA; e = (np.arange(nE) - nE // 2) * hE
    D1, D2 = np.meshgrid(a, e, indexing='ij'); Q = GAM / 2 * (SAA * D1 ** 2 + 2 * SAE * D1 * D2 + SEE * D2 ** 2)
    law = [((mA, mE), (1 + r) / 4), ((-mA, -mE), (1 + r) / 4), ((mA, -mE), (1 - r) / 4), ((-mA, mE), (1 - r) / 4)]
    resA = hA + abs(SAE) * GAM * hE / cres; resE = hE + abs(SAE) * GAM * hA / cresE
    iA0, iA1 = 3 * mA + 3, nA - 3 * mA - 3; jE0, jE1 = 3 * mE + 3, nE - 3 * mE - 3
    sg = np.sign(corr); st = dict(args=args, fund_bands=0, etf_bands=0, nc_f=0, nc_e=0, wrong_f=0, wrong_f_strict=0, pairs_f=0, wrong_e=0, pairs_e=0,
                                   const_f=True, const_e=True, nt=0, nt_mis=0, med_n=0, med_max=0.0, med_excl=0, pt_out=0, pt_in_trade=0, frictionless=kEp + kEm == 0)
    Vn = None
    for t in reversed(range(T)):
        W = Q.copy()
        if Vn is not None: W += sum(p * shift(Vn, i, j) for (i, j), p in law)
        U = l1min(W, kEp, kEm, hE, 1); V = l1min(U, kAp, kAm, hA, 0)
        tol = 1e-12 * np.abs(W).max()
        fh = U - V <= tol; eh = W - U <= tol; fh_s = U - V <= 0.0
        nt = W - V <= tol
        cols = np.arange(max(jE0, 0), min(jE1, nE)); rows = np.arange(max(iA0, 0), min(iA1, nA))
        if len(cols) < 2 or len(rows) < 2: Vn = V; continue
        # fund bands per column (rows restricted to the usable range)
        for mask, key in ((fh, 'wrong_f'), (fh_s, 'wrong_f_strict')):
            f, l, c = bands(mask[np.ix_(rows, cols)], 0)
            ok = c & (f > 0) & (l < len(rows) - 1)
            if key == 'wrong_f':
                ncn = int((~c & mask[np.ix_(rows, cols)].any(0)).sum())
                st['fund_bands'] += int(ok.sum()); st['nc_f'] += ncn
                if ncn: st.setdefault('nc_where', []).append((t, ncn))
                F, L, OK = f, l, ok
            d_ok = ok[1:] & ok[:-1]; df, dl = np.diff(f)[d_ok], np.diff(l)[d_ok]
            if key == 'wrong_f': st['pairs_f'] += int(d_ok.sum())
            if sg > 0: st[key] += int((df > 0).sum() + (dl > 0).sum())
            elif sg < 0: st[key] += int((df < 0).sum() + (dl < 0).sum())
            elif key == 'wrong_f': st['const_f'] &= bool(np.all(df == 0) and np.all(dl == 0))
        if kEp + kEm > 0:
            f, l, c = bands(eh[np.ix_(rows, cols)], 1); ok = c & (f > 0) & (l < len(cols) - 1)
            st['etf_bands'] += int(ok.sum()); st['nc_e'] += int((~c & eh[np.ix_(rows, cols)].any(1)).sum())
            d_ok = ok[1:] & ok[:-1]; df, dl = np.diff(f)[d_ok], np.diff(l)[d_ok]; st['pairs_e'] += int(d_ok.sum())
            if sg > 0: st['wrong_e'] += int((df > 0).sum() + (dl > 0).sum())
            elif sg < 0: st['wrong_e'] += int((df < 0).sum() + (dl < 0).sum())
            else: st['const_e'] &= bool(np.all(df == 0) and np.all(dl == 0))
            # 2d: NT (values) = {fund held in its column} and {ETF held in its row}, on the usable block
            sub = np.ix_(rows, cols); pred = fh[sub] & eh[sub]
            st['nt'] += int(nt[sub].sum()); st['nt_mis'] += int((pred != nt[sub]).sum())
        if t == T - 1 and kEp + kEm > 0:
            lob, los = -(kAp - rho * kEp) / cres, -(kAp + rho * kEm) / cres; hib, his = (kAm + rho * kEp) / cres, (kAm - rho * kEm) / cres
            for jj, j in enumerate(cols):
                if not OK[jj]: continue
                lo_i, hi_i = rows[F[jj]], rows[L[jj]]; interior = True
                for ia in (lo_i, hi_i):
                    obj = W[ia, :] + np.where(e > e[j], kEp * (e - e[j]), kEm * (e[j] - e)); k = int(np.argmin(obj))
                    interior &= 3 * mE < k < nE - 3 * mE
                if not interior: st['med_excl'] += 1; continue
                loi = -rhoA * e[j] - kAp / (GAM * SAA); hii = -rhoA * e[j] + kAm / (GAM * SAA)
                err = max(abs(a[lo_i] - np.median([lob, loi, los])), abs(a[hi_i] - np.median([hib, hii, his]))) / resA
                st['med_n'] += 1; st['med_max'] = max(st['med_max'], err)
            # 1c: NT at the last review vs the static parallelotope x* + (gamma S)^{-1} ([-kA+, kA-] x [-kE+, kE-])
            sub = np.ix_(rows, cols); X1, X2 = D1[sub], D2[sub]; y1 = GAM * (S[0, 0] * X1 + S[0, 1] * X2); y2 = GAM * (S[1, 0] * X1 + S[1, 1] * X2)
            sl1 = GAM * (abs(S[0, 0]) * hA + abs(S[0, 1]) * hE); sl2 = GAM * (abs(S[1, 0]) * hA + abs(S[1, 1]) * hE)
            inside = (y1 >= -kAp + sl1) & (y1 <= kAm - sl1) & (y2 >= -kEp + sl2) & (y2 <= kEm - sl2)   # gamma Sigma d in [-k+, k-]
            outside = (y1 < -kAp - sl1) | (y1 > kAm + sl1) | (y2 < -kEp - sl2) | (y2 > kEm + sl2)
            st['pt_out'] += int((nt[sub] & outside).sum()); st['pt_in_trade'] += int((~nt[sub] & inside).sum())
        Vn = V
    return st


def cells():
    C = [c for c in R36.cells()]
    for corr in [-0.5, -0.9]:
        for kA in [0.001, 0.005]:
            for kE in [0.0002, 0.001, 0.005]:
                for r in [-0.8, 0, 0.8]:
                    C.append((corr, kA, kA, kE, kE, r, 0.5))
    return C


def main():
    C = cells()
    with Pool(6) as p: R = p.map(cell, C, chunksize=1)
    s = lambda k: sum(x[k] for x in R)
    print(f"{len(R)} cells (036's 216 and 36 mirror cells), {T} reviews")
    print(f"fund bands {s('fund_bands')} ({s('nc_f')} non-contiguous set aside); ETF bands {s('etf_bands')} ({s('nc_e')} non-contiguous)")
    print(f"part 1 medians: {s('med_n')} columns ({s('med_excl')} excluded, ETF optimizer at the grid edge); max error {max(x['med_max'] for x in R):.2f} res_A")
    print(f"part 1c: last-review no-trade points outside the static parallelotope {s('pt_out')}; points inside it (off its boundary) that trade {s('pt_in_trade')}")
    print(f"part 2b: wrong-direction fund-edge steps {s('wrong_f')} of {s('pairs_f')} adjacent pairs (tolerance); with strict equality {s('wrong_f_strict')}")
    print(f"part 2c: wrong-direction ETF-edge steps {s('wrong_e')} of {s('pairs_e')}")
    z = [x for x in R if x['args'][0] == 0]
    print(f"corr 0: fund edges constant in every cell {all(x['const_f'] for x in z)}; ETF edges constant {all(x['const_e'] for x in z if not x['frictionless'])}")
    fr = [x for x in R if x['frictionless']]
    print(f"frictionless ETF: fund edges wrong-direction {sum(x['wrong_f'] for x in fr)}, constant (corr 0) {all(x['const_f'] for x in fr if x['args'][0] == 0)}")
    for x in R:
        if x.get('nc_where'): print('  non-contiguous fund bands in', x['args'], 'at (review, count)', x['nc_where'][:4])
    print(f"part 2d: {s('nt')} no-trade points (values); mismatches with the band intersection {s('nt_mis')}")


if __name__ == "__main__":
    main()
