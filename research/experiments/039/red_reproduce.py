"""Red's reproduction of experiment 039 (and its addendum), written without reading analyze.py or addendum.py.
Red's own exact two-instrument DP (the transforms and grid rule of red's 036/042 reproductions; argument 1 is a directory
holding red_reproduce.py from experiment 036 and red042.py from experiment 042), at every usable ETF column. The
future-idle share is computed exactly by a backward recursion along the r = 0 target lattice through the optimal policy
(fund clipped to its band in the ETF incumbent's column, then the ETF clipped to its band in the fund's row)."""
import sys; sys.path.insert(0, sys.argv[1])
import numpy as np
from multiprocessing import Pool
from scipy.stats import spearmanr
import red_reproduce as R36
from red_reproduce import l1min, shift
import red042 as R42
GAM, SAA, SEE, T = R36.GAM, R36.SAA, R36.SEE, R36.T


def band_idx(mask, axis):
    m = mask if axis == 0 else mask.T
    n = m.shape[0]; anyh = m.any(0); first = np.argmax(m, 0); last = n - 1 - np.argmax(m[::-1], 0)
    contig = anyh & (m.sum(0) == last - first + 1)
    return first, last, contig


def solve(args):
    corr, kAp, kAm, kEp, kEm, r, step = args
    S, SAE, cres, hA, hE, mA, mE, nA, nE = R42.grid(args)
    a = (np.arange(nA) - nA // 2) * hA; e = (np.arange(nE) - nE // 2) * hE
    D1, D2 = np.meshgrid(a, e, indexing='ij'); Q = GAM / 2 * (SAA * D1 ** 2 + 2 * SAE * D1 * D2 + SEE * D2 ** 2)
    law = [((mA, mE), (1 + r) / 4), ((-mA, -mE), (1 + r) / 4), ((mA, -mE), (1 - r) / 4), ((-mA, mE), (1 - r) / 4)]
    Vn = None; per = {}
    for t in reversed(range(T)):
        W = Q.copy()
        if Vn is not None: W += sum(p * shift(Vn, i, j) for (i, j), p in law)
        U = l1min(W, kEp, kEm, hE, 1); V = l1min(U, kAp, kAm, hA, 0); tol = 1e-12 * np.abs(W).max()
        flo, fhi, fc = band_idx(U - V <= tol, 0)          # fund band per ETF column
        elo, ehi, ec = band_idx(W - U <= tol, 1)          # ETF band per fund row
        # ETF direction at the fund's edges (post-trade ETF = clip of the incumbent to its band in the edge row)
        cols = np.arange(nE)
        dir_lo = np.sign(np.clip(cols, elo[flo], ehi[flo]) - cols); dir_hi = np.sign(np.clip(cols, elo[fhi], ehi[fhi]) - cols)
        per[t] = dict(flo=flo, fhi=fhi, fc=fc, elo=elo, ehi=ehi, ec=ec, dlo=dir_lo, dhi=dir_hi)
        Vn = V
    return dict(args=args, a=a, e=e, hA=hA, mA=mA, mE=mE, nA=nA, nE=nE, cres=cres, SAE=SAE, per=per)


def future_idle(o):
    """H_s(i, j) = sum over reviews s..T-1 of 1{ETF idle at both fund edges at the pre-trade ETF column}, expected along the
    r = 0 lattice under the optimal policy; returns the start-of-review arrays."""
    nA, nE, mA, mE, per = o['nA'], o['nE'], o['mA'], o['mE'], o['per']
    I_, J_ = np.meshgrid(np.arange(nA), np.arange(nE), indexing='ij'); H = {T: np.zeros((nA, nE))}
    post = {}
    for s in reversed(range(T)):
        P = per[s]; idle = ((P['dlo'] == 0) & (P['dhi'] == 0) & P['fc']).astype(float)
        ia = np.clip(I_, P['flo'][J_], P['fhi'][J_]); jp = np.clip(J_, P['elo'][ia], P['ehi'][ia]); post[s] = (ia, jp)
        nxt = 0.25 * sum(H[s + 1][np.clip(ia - da, 0, nA - 1), np.clip(jp - de, 0, nE - 1)] for da in (mA, -mA) for de in (mE, -mE))
        H[s] = idle[J_] + nxt
    return H, post


def cell_pairs(key):
    corr, kAp, kAm, kEp, kEm, step = key
    o0 = solve((corr, kAp, kAm, kEp, kEm, 0.0, step)); H, post = future_idle(o0)
    ceil = (kAp + kAm) / o0['cres']; alone = (kAp + kAm) / (GAM * SAA)
    rhoAB = o0['SAE'] / SAA; uA, uE = step * ceil, step * (kEp + kEm) / (GAM * SEE); vA, vB = uA ** 2, uE ** 2
    vid = lambda rr: vA + rhoAB ** 2 * vB + 2 * rhoAB * rr * np.sqrt(vA * vB)
    nA, nE, mA, mE = o0['nA'], o0['nE'], o0['mA'], o0['mE']; a = o0['a']
    jlo, jhi = 3 * mE + 3, nE - 3 * mE - 3; ilo, ihi = 3 * mA + 3, nA - 3 * mA - 3
    out = []
    for r in (-0.8, 0.8):
        o1 = solve((corr, kAp, kAm, kEp, kEm, r, step))
        for t in range(T):
            P0, P1 = o0['per'][t], o1['per'][t]
            for j in range(jlo, jhi):
                if not (P0['fc'][j] and P1['fc'][j]): continue
                if not (ilo < P0['flo'][j] and P0['fhi'][j] < ihi): continue
                reg = lambda P: 'idle' if (P['dlo'][j] == 0 and P['dhi'][j] == 0) else ('rehedge' if (P['dlo'][j] != 0 and P['dhi'][j] != 0) else 'mixed')
                g0, g1 = reg(P0), reg(P1)
                if g0 != g1: continue
                w0 = a[P0['fhi'][j]] - a[P0['flo'][j]]; w1 = a[P1['fhi'][j]] - a[P1['flo'][j]]
                if w0 <= 0: continue
                # future-idle share from the post-trade state at each fund edge (reviews t+1..T-1), and the next-review idle probability
                sh = nx = 0.0
                if t < T - 1:
                    for ie in (P0['flo'][j], P0['fhi'][j]):
                        jp = int(np.clip(j, P0['elo'][ie], P0['ehi'][ie]))
                        cont = 0.25 * sum(H[t + 1][int(np.clip(ie - da, 0, nA - 1)), int(np.clip(jp - de, 0, nE - 1))] for da in (mA, -mA) for de in (mE, -mE))
                        P2 = o0['per'][t + 1]; idle2 = (P2['dlo'] == 0) & (P2['dhi'] == 0) & P2['fc']
                        nxt = 0.25 * sum(float(idle2[int(np.clip(jp - de, 0, nE - 1))]) for da in (mA, -mA) for de in (mE, -mE))
                        sh += cont / (T - 1 - t) / 2; nx += nxt / 2
                out.append(dict(corr=corr, step=step, t=t, r=r, reg=g0, lr=float(np.log(w1 / w0)), res=o0['hA'] / w0, wc=w0 / ceil, wa=w0 / alone,
                                share=sh, nxt=nx, pred=float(np.log((vid(r) / vid(0.0)) ** (1 / 3))), sAE=np.sign(o0['SAE'])))
    return out


def main():
    keys = [(corr, kA, kA, kE, kE, step) for corr in [0.5, 0.9, 0.97] for kA in [0.001, 0.005] for kE in [0.0002, 0.001, 0.005] for step in [0.5, 0.1]]
    keys += [(corr, 0.01, 0.0, 0.0005, 0.0005, step) for corr in [0.5, 0.9, 0.97] for step in [0.5, 0.1]]
    with Pool(6) as p: P = [x for L in p.map(cell_pairs, keys, chunksize=1) for x in L]
    moved = lambda x: abs(x['lr']) > 2 * x['res']
    RH = [x for x in P if x['reg'] == 'rehedge' and x['wc'] < 0.9 and x['t'] <= T - 2]
    print(f"re-hedge pairs (corr > 0, not coarse, reviews 0-{T - 2}): {len(RH)}")
    rho, _ = spearmanr([abs(x['lr']) for x in RH], [x['share'] for x in RH]); print(f"item 2: Spearman(|log ratio|, future-idle share) = {rho:+.2f}")
    print("  by t: " + ", ".join(f"t {t}: {spearmanr([abs(x['lr']) for x in RH if x['t'] == t], [x['share'] for x in RH if x['t'] == t])[0]:+.2f}" for t in range(T - 1)))
    for lo, hi, lab in [(-1, 1e-12, '0'), (0.1, 0.3, '(0.1, 0.3]'), (0.3, 0.6, '(0.3, 0.6]'), (0.6, 1.01, '(0.6, 1]')]:
        B = [x for x in RH if (x['share'] == 0 if lab == '0' else lo < x['share'] <= hi)]
        if B: print(f"  share {lab}: {len(B)} pairs, moved {np.mean([moved(x) for x in B]):.2f}, median |log ratio| {np.median([abs(x['lr']) for x in B]):.3f}, mean {np.mean([abs(x['lr']) for x in B]):.3f}")
    print(f"  pairs with share in (0, 0.1]: {sum(0 < x['share'] <= 0.1 for x in RH)}")
    cells = {}
    for x in RH: cells.setdefault((x['corr'], x['step'], x['t']), []).append(moved(x))
    ks = sorted(cells); rho1, pv = spearmanr([np.mean(cells[k]) for k in ks], [T - 1 - k[2] for k in ks])
    print(f"item 1: Spearman(share moved, remaining reviews) = {rho1:+.2f} (p = {pv:.2f}) over {len(ks)} (corr, step, t) cells")
    last = [x for x in P if x['t'] == T - 1]; print(f"addendum (i): one remaining review: {len(last)} pairs, max |log ratio| {max(abs(x['lr']) for x in last):.1e}")
    print("addendum (ii): re-hedge share moved by remaining reviews: " + ", ".join(f"{T - t}: {np.mean([moved(x) for x in P if x['reg'] == 'rehedge' and x['wc'] < 0.9 and x['t'] == t]):.2f}" for t in range(T - 1, -1, -1)))
    rho2, _ = spearmanr([abs(x['lr']) for x in RH], [x['nxt'] for x in RH]); print(f"  Spearman(|log ratio|, next-review idle probability) = {rho2:+.2f}")
    mv = [x for x in RH if moved(x)]; print(f"  moved re-hedge pairs with the sign of r Sigma_AE: {sum(np.sign(x['lr']) == np.sign(x['r'] * x['sAE']) for x in mv)}/{len(mv)}")
    ID = [x for x in P if x['reg'] == 'idle' and x['wa'] < 0.9 and abs(x['pred']) > 0.01 and x['t'] <= T - 2]
    print(f"addendum (iii): {len(ID)} idle fine pairs; slope of log observed on log predicted by future-idle share: " +
          ", ".join(f"[{lo}, {hi}]: {np.polyfit([x['pred'] for x in B], [x['lr'] for x in B], 1)[0]:.2f} ({len(B)})" for lo, hi in [(0, 0.5), (0.5, 0.75), (0.75, 0.9), (0.9, 1.0)]
                    for B in [[x for x in ID if lo <= x['share'] <= hi]] if len(B) > 2))


if __name__ == "__main__":
    main()
