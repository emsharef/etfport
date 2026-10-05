"""Red's reproduction of experiment 038, written without reading analyze.py. Instead of 036's summary.json it uses red's own
exact two-instrument DP from its experiment 036 reproduction (argument 1: the directory holding that red_reproduce.py),
pairs bands at r = +-0.8 with r = 0 at equal inputs, and applies the Design's regimes and statistics."""
import sys; sys.path.insert(0, sys.argv[1])
import numpy as np
from multiprocessing import Pool
import red_reproduce as R36   # red's experiment 036 DP (cell, cells, constants)


def run():
    C = [c for c in R36.cells() if c[3] + c[4] > 0]
    with Pool(6) as p: out = p.map(R36.cell, C, chunksize=1)
    return {o['args']: o for o in out}


def main():
    D = run(); pairs = []
    for args, o in D.items():
        corr, kAp, kAm, kEp, kEm, r, step = args
        if r == 0: continue
        o0 = D[(corr, kAp, kAm, kEp, kEm, 0.0, step)]
        SAE = corr * np.sqrt(R36.SAA * R36.SEE); rhoAB = SAE / R36.SAA
        uA, uE = step * o['ceil'], step * ((kEp + kEm) / (R36.GAM * R36.SEE))
        vA, vB = uA ** 2, uE ** 2
        vid = lambda rr: vA + rhoAB ** 2 * vB + 2 * rhoAB * rr * np.sqrt(vA * vB)
        pred_idle = (vid(r) / vid(0.0)) ** (1 / 3)
        for R, R0 in zip(o['res'], o0['res']):
            if R['t'] == R36.T - 1: continue
            b0 = {w['j']: w for w in R0['rows'] if w['contig'] and not w['etf_edge']}
            for w in R['rows']:
                if not w['contig'] or w['etf_edge'] or w['j'] not in b0: continue
                w0 = b0[w['j']]
                reg0 = 'idle' if (w0['hi_dir'] == 0 and w0['lo_dir'] == 0) else ('rehedge' if (w0['hi_dir'] != 0 and w0['lo_dir'] != 0) else 'mixed')
                reg1 = 'idle' if (w['hi_dir'] == 0 and w['lo_dir'] == 0) else ('rehedge' if (w['hi_dir'] != 0 and w['lo_dir'] != 0) else 'mixed')
                if reg0 != reg1: continue
                W, W0 = w['hi'] - w['lo'], w0['hi'] - w0['lo']
                if W0 <= 0: continue
                pairs.append(dict(corr=corr, step=step, r=r, reg=reg0, obs=W / W0, pred=pred_idle if reg0 == 'idle' else 1.0, res=o['hA'] / W0,
                                  wc=W0 / o['ceil'], wa=W0 / o['alone'], sAE=np.sign(SAE)))
    print(f"{len(pairs)} band pairs (reviews 0-6, ETF rate > 0, same regime at both r)")
    print("idle, fine (corr > 0, |log pred| > 0.01, width below the fund-alone width):")
    for corr in [0.5, 0.9, 0.97]:
        for step in [0.1, 0.5]:
            P = [p for p in pairs if p['reg'] == 'idle' and p['corr'] == corr and p['step'] == step and abs(np.log(p['pred'])) > 0.01 and p['wa'] < 0.9]
            if not P: continue
            lo, lp = np.log([p['obs'] for p in P]), np.log([p['pred'] for p in P])
            moved = np.abs(lo) > 2 * np.array([p['res'] for p in P])
            sign = np.mean(np.sign(lo[moved]) == np.sign(lp[moved])) if moved.any() else np.nan
            slope = np.polyfit(lp, lo, 1)[0] if len(P) > 2 else np.nan
            print(f"  corr {corr}, step {step}: {len(P)} pairs; median |log err| prediction {np.median(np.abs(lo - lp)):.3f}, null {np.median(np.abs(lo)):.3f}; sign agreement {sign:.2f} ({moved.sum()} moved); slope {slope:.2f}")
    Pc = [p for p in pairs if p['reg'] == 'idle' and p['corr'] > 0 and p['wa'] >= 0.9]
    print(f"idle, coarse (width >= 0.9 fund-alone): {len(Pc)} pairs, moved beyond two grid steps {sum(abs(np.log(p['obs'])) > 2 * p['res'] for p in Pc)}")
    Pr = [p for p in pairs if p['reg'] == 'rehedge' and p['corr'] > 0 and p['wc'] < 0.9]
    mv = [p for p in Pr if abs(np.log(p['obs'])) > 2 * p['res']]
    print(f"re-hedge (corr > 0, not coarse): {len(Pr)} pairs; moved beyond two grid steps {len(mv) / len(Pr):.0%}; median |log ratio| among moved {np.median([abs(np.log(p['obs'])) for p in mv]):.3f}, "
          f"90th pct {np.percentile([abs(np.log(p['obs'])) for p in mv], 90):.3f}; sign = sign(r Sigma_AE) at {np.mean([np.sign(np.log(p['obs'])) == np.sign(p['r'] * p['sAE']) for p in mv]):.2f}")
    for corr in [0.5, 0.9, 0.97]:
        for step in [0.1, 0.5]:
            Q = [p for p in Pr if p['corr'] == corr and p['step'] == step]
            if Q: print(f"  corr {corr}, step {step}: {len(Q)} pairs, moved {np.mean([abs(np.log(p['obs'])) > 2 * p['res'] for p in Q]):.0%}")


if __name__ == "__main__":
    main()
