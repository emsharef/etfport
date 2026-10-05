"""Experiment 042: claim 108 parts 1-2 (the dynamic shape of the bundling band) against experiment 036's exact
two-instrument dynamic program. Registered design: experiments/042-claim108-dynamic-shape-check.md.
Run: uv run python experiments/042/run.py

The model, grid and Bellman step are experiment 036's (deviation coordinates, fixed Sigma, beta = 1, no marking; exact
L1 transforms along the ETF axis, then the fund axis, experiment 023's fastdp.l1). Here every ETF column and fund row
away from the grid edges is measured, at every review.
"""
import importlib.util
import json
import multiprocessing as mp
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("run036", HERE.parent / "036" / "run.py")
r036 = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(r036)
fastdp = r036.fastdp
GAMMA, BETA, T, SAA, SEE, CAP = r036.GAMMA, r036.BETA, r036.T, r036.SAA, r036.SEE, r036.CAP


def grid(corr, kA, kE, step, hfac):
    """Experiment 036's grid (run_cell's lines, unchanged)."""
    S, cres, rho = r036.setup(corr, kA, kE)
    vmin, vmax = r036.extent(S, kA, kE)
    span = (vmax - vmin) * 1.2
    wA = (kA[0] + kA[1]) / cres
    wE = (kE[0] + kE[1]) / (GAMMA * SEE) if kE[0] + kE[1] > 0 else 2 * 0.001 / (GAMMA * SEE)
    uA, uE = step * wA, step * wE
    hA = max(wA / 100, 1.4 * span[0] / CAP) / hfac; hE = max(wE / 100, 1.4 * span[1] / CAP) / hfac
    sA, sE = max(1, round(uA / hA)), max(1, round(uE / hE))
    mA = int(np.ceil((max(-vmin[0], vmax[0]) * 1.2 + 3 * sA * hA) / hA)); mE = int(np.ceil((max(-vmin[1], vmax[1]) * 1.2 + 3 * sE * hE) / hE))
    return S, cres, rho, hA, hE, sA, sE, np.arange(-mA, mA + 1) * hA, np.arange(-mE, mE + 1) * hE


def bands(held):
    """Per column (axis 1) of a boolean held array: first and last held row, and contiguity."""
    any_ = held.any(0)
    lo = np.argmax(held, 0); hi = held.shape[0] - 1 - np.argmax(held[::-1], 0)
    contig = held.sum(0) == hi - lo + 1
    return lo, hi, any_ & contig, any_ & ~contig


def run_cell(args):
    corr, kA, kE, r, step, hfac = args
    S, cres, rho, hA, hE, sA, sE, dA, dE = grid(corr, kA, kE, step, hfac)
    SAE = S[0, 1]; rhoA = SAE / SAA
    cresE = GAMMA * SEE * (1 - corr ** 2)
    nA, nE = len(dA), len(dE); iA, iE = np.arange(nA), np.arange(nE)
    YA, YE = np.meshgrid(dA, dE, indexing="ij")
    quad = -0.5 * GAMMA * (S[0, 0] * YA ** 2 + 2 * S[0, 1] * YA * YE + S[1, 1] * YE ** 2)
    law = [((+1, +1), (1 + r) / 4), ((-1, -1), (1 + r) / 4), ((+1, -1), (1 - r) / 4), ((-1, +1), (1 - r) / 4)]
    resA = hA + abs(SAE) * GAMMA * hE / cres
    resE = hE + abs(SAE) * GAMMA * hA / cresE if kE[0] + kE[1] > 0 else None
    colin = (iE > 3 * sE) & (iE < nE - 1 - 3 * sE); rowin = (iA > 3 * sA) & (iA < nA - 1 - 3 * sA)
    sgn = np.sign(SAE) if corr != 0 else 0
    V = np.zeros_like(quad); rows = []
    for t in range(T - 1, -1, -1):
        cont = np.zeros_like(V)
        if t < T - 1:
            P = np.pad(V, ((sA, sA), (sE, sE)), mode="edge")
            for (a, e), pr in law:
                cont += pr * P[sA - a * sA: sA - a * sA + nA, sE - e * sE: sE - e * sE + nE]
        W = quad + BETA * cont
        Z, AE = fastdp.l1(W, kE[0] * hE, kE[1] * hE, axis=1)
        U, AA = fastdp.l1(Z, kA[0] * hA, kA[1] * hA, axis=0)
        V = U
        rec = dict(t=t)
        tol = 1e-12 * max(1.0, np.abs(W).max())
        # Deviation 1: a holding is held when staying attains the optimum within tol (exact ties on the lattice are held);
        # the policy's own tie-break (floating point) is kept as a secondary count
        fheld = Z - U >= -tol; eheld = W - Z >= -tol
        rawf = raw_fund_wrong(AA, iA, colin, sA, nA, sgn)
        rec["fund_wrong_raw"] = rawf
        # fund band per ETF column; ETF band per fund row
        flo, fhi, fok, fnc = bands(fheld)
        fin = fok & colin & (flo > 3 * sA) & (fhi < nA - 1 - 3 * sA)
        rec["fund_cols"] = int(fin.sum()); rec["fund_noncontig"] = int((fnc & colin).sum())
        # part 2b: wrong-direction steps of the fund's edges across adjacent usable columns
        pair = fin[:-1] & fin[1:]
        dlo, dhi = np.diff(flo)[pair], np.diff(fhi)[pair]
        if sgn > 0:
            wl, wh = dlo, dhi
        elif sgn < 0:
            wl, wh = -dlo, -dhi
        else:
            wl = wh = None
        if kE[0] + kE[1] == 0 or sgn == 0:        # frictionless ETF (claim 107 part 3) or Sigma_AE = 0: constant edges
            rec["fund_const"] = bool(np.ptp(flo[fin]) == 0 and np.ptp(fhi[fin]) == 0) if fin.any() else None
            rec["fund_range"] = int(max(np.ptp(flo[fin]), np.ptp(fhi[fin]))) if fin.any() else None
        if wl is not None:
            rec["fund_wrong"] = int((wl > 0).sum() + (wh > 0).sum()); rec["fund_wrong2"] = int((wl > 1).sum() + (wh > 1).sum())
            rec["fund_pairs"] = int(2 * pair.sum())
        # observed slope bound: secant over ten ETF columns
        if sgn != 0 and fin.sum() > 10:
            jj = np.nonzero(fin)[0]; ok = np.isin(jj + 10, jj); j0 = jj[ok]
            if j0.size:
                sl = np.maximum(np.abs(dA[flo[j0 + 10]] - dA[flo[j0]]), np.abs(dA[fhi[j0 + 10]] - dA[fhi[j0]])) / (10 * hE)
                rec["slope_max"] = float(sl.max()); rec["rhoA"] = float(abs(rhoA))
                rec["slope_res"] = float(resA / (10 * hE))
        if kE[0] + kE[1] > 0:
            elo, ehi, eok, enc = bands(eheld.T)                      # ETF band per fund row
            ein = eok & rowin & (elo > 3 * sE) & (ehi < nE - 1 - 3 * sE)
            rec["etf_rows"] = int(ein.sum()); rec["etf_noncontig"] = int((enc & rowin).sum())
            pe = ein[:-1] & ein[1:]
            el, eh = np.diff(elo)[pe], np.diff(ehi)[pe]
            if sgn > 0:
                rec["etf_wrong"] = int((el > 0).sum() + (eh > 0).sum()); rec["etf_wrong2"] = int((el > 1).sum() + (eh > 1).sum())
            elif sgn < 0:
                rec["etf_wrong"] = int((el < 0).sum() + (eh < 0).sum()); rec["etf_wrong2"] = int((el < -1).sum() + (eh < -1).sum())
            else:
                rec["etf_const"] = bool(np.ptp(elo[ein]) == 0 and np.ptp(ehi[ein]) == 0) if ein.any() else None
            rec["etf_pairs"] = int(2 * pe.sum())
        # part 2d: no-trade region (stay value attains the optimum) against the intersection of the two bands
        inner = rowin[:, None] & colin[None, :]
        nt = (V - W) <= tol
        inter = fheld & eheld
        rec["nt_points"] = int((nt & inner).sum()); rec["nt_mismatch"] = int(((nt != inter) & inner).sum())
        if t == T - 1:
            rec.update(part1(dA, dE, AA, AE, flo, fhi, fin, S, cres, cresE, rho, rhoA, kA, kE, resA, hA, hE, sE, nE, nt, inner))
        rows.append(rec)
    return dict(corr=corr, kA=list(kA), kE=list(kE), r=r, step=step, hfac=hfac, hA=hA, hE=hE, resA=resA, resE=resE,
                rho=rho, rhoA=rhoA, cres=cres, cresE=cresE, rows=rows[::-1])


def raw_fund_wrong(AA, iA, colin, sA, nA, sgn):
    """Part 2b's count with the policy's own tie-break (held = the policy does not trade)."""
    if sgn == 0:
        return None
    flo, fhi, fok, _ = bands(AA == iA[:, None])
    fin = fok & colin & (flo > 3 * sA) & (fhi < nA - 1 - 3 * sA)
    pair = fin[:-1] & fin[1:]
    d = np.concatenate([np.diff(flo)[pair], np.diff(fhi)[pair]]) * sgn
    return int((d > 0).sum())


def part1(dA, dE, AA, AE, flo, fhi, fin, S, cres, cresE, rho, rhoA, kA, kE, resA, hA, hE, sE, nE, nt, inner):
    out = {}
    j = np.nonzero(fin)[0]
    # hypothesis: ETF optimizer interior at both fund edges (more than 3 ETF steps inside the grid)
    ok = np.array([(3 * sE < AE[flo[k], k] < nE - 1 - 3 * sE) and (3 * sE < AE[fhi[k], k] < nE - 1 - 3 * sE) for k in j], bool) if j.size else np.zeros(0, bool)
    out["p1_excluded"] = int((~ok).sum()); j = j[ok]
    p = dE[j]
    lo_i = -rhoA * p - kA[0] / (GAMMA * S[0, 0]); hi_i = -rhoA * p + kA[1] / (GAMMA * S[0, 0])
    lo_b = -(kA[0] - rho * kE[0]) / cres; lo_s = -(kA[0] + rho * kE[1]) / cres
    hi_b = (kA[1] + rho * kE[0]) / cres; hi_s = (kA[1] - rho * kE[1]) / cres
    Lf = np.median(np.stack([np.full_like(p, lo_b), lo_i, np.full_like(p, lo_s)]), 0)
    Hf = np.median(np.stack([np.full_like(p, hi_b), hi_i, np.full_like(p, hi_s)]), 0)
    eL, eH = dA[flo[j]] - Lf, dA[fhi[j]] - Hf
    err = np.maximum(np.abs(eL), np.abs(eH)) / resA
    out["p1_cols"] = int(j.size); out["p1_err_max"] = float(err.max()) if j.size else None
    out["p1_beyond1"] = int((err > 1).sum()); out["p1_beyond2"] = int((err > 2).sum())
    # regimes (1b), read off the formula: which of the three numbers is the median at each edge
    def which(med, b, idle, s):
        same = np.isclose(b, s, rtol=0, atol=1e-15)                  # frictionless ETF: one re-hedge level
        return np.where(np.isclose(med, b, rtol=0, atol=1e-15), "b", np.where(np.isclose(med, s, rtol=0, atol=1e-15) & ~same, "s", "i"))
    rl, rh = which(Lf, lo_b, lo_i, lo_s), which(Hf, hi_b, hi_i, hi_s)
    wf = Hf - Lf; wd = dA[fhi[j]] - dA[flo[j]]
    reg = {}
    for key, name in ((("b", "b"), "both bought"), (("s", "s"), "both sold"), (("i", "i"), "both idle"), (("b", "s"), "bought/sold"), (("s", "b"), "sold/bought")):
        m = (rl == key[0]) & (rh == key[1])
        if m.any():
            reg[name] = dict(n=int(m.sum()), err_max=float(np.abs(wd[m] - wf[m]).max() / resA))
    m = ~((rl == rh) | ((rl == "b") & (rh == "s")) | ((rl == "s") & (rh == "b")))
    if m.any():
        reg["mixed"] = dict(n=int(m.sum()), err_max=float(np.abs(wd[m] - wf[m]).max() / resA))
    out["p1_regimes"] = reg
    # formula widths by regime against the Statement's 1b expressions
    kAs, kEs = kA[0] + kA[1], kE[0] + kE[1]
    exp = {"both bought": kAs / cres, "both sold": kAs / cres, "both idle": kAs / (GAMMA * S[0, 0]),
           "bought/sold": (kAs - abs(rho) * kEs) / cres, "sold/bought": (kAs - abs(rho) * kEs) / cres}
    out["p1_1b_formula_err"] = float(max([np.abs(wf[(rl == k[0]) & (rh == k[1])] - exp[n]).max()
                                          for k, n in ((("b", "b"), "both bought"), (("s", "s"), "both sold"), (("i", "i"), "both idle"))
                                          if ((rl == k[0]) & (rh == k[1])).any()] + [0.0]))
    # the bend (1a), for each edge: fit a line on the columns strictly between both DP flats, intersect with the flats
    out["bend"] = []
    if kEs > 0 and rhoA != 0 and j.size > 5:
        Lf_len = kEs / cresE
        out["bend_identity"] = float(max(abs((lo_b - lo_s) / rhoA - Lf_len), abs((hi_b - hi_s) / rhoA - Lf_len)) / Lf_len)
        for name, edge, b, s in (("lo", dA[flo[j]], lo_b, lo_s), ("hi", dA[fhi[j]], hi_b, hi_s)):
            # flats seen at the extreme usable columns must be on flats by the formula
            fl = edge[0]; fr = edge[-1]
            on_l = abs(fl - (b if rhoA > 0 else s)) <= 2 * resA; on_r = abs(fr - (s if rhoA > 0 else b)) <= 2 * resA
            mid = (np.abs(edge - fl) > 2 * resA) & (np.abs(edge - fr) > 2 * resA)
            if abs(b - s) < 6 * resA:                                   # the bend's drop spans under 6 resolutions
                out["bend"].append(dict(edge=name, usable=False, why="below resolution")); continue
            if not (on_l and on_r) or mid.sum() < 3:
                out["bend"].append(dict(edge=name, usable=False, why="flats not both in range")); continue
            sl, ic = np.polyfit(p[mid], edge[mid], 1)
            pl, pr = (fl - ic) / sl, (fr - ic) / sl
            out["bend"].append(dict(edge=name, usable=True, length=float(abs(pr - pl)), formula=float(Lf_len),
                                    tol=float(2 * hE + 2 * resA / abs(rhoA)), slope=float(sl), rhoA=float(rhoA), n_mid=int(mid.sum())))
    # 1c: last-review no-trade set against the static parallelotope, both directions
    YA, YE = np.meshgrid(dA, dE, indexing="ij")
    GA = GAMMA * (S[0, 0] * YA + S[0, 1] * YE); GE = GAMMA * (S[0, 1] * YA + S[1, 1] * YE)
    tA = GAMMA * (abs(S[0, 0]) * hA + abs(S[0, 1]) * hE); tE = GAMMA * (abs(S[0, 1]) * hA + abs(S[1, 1]) * hE)
    insd = (GA >= -kA[0] + tA) & (GA <= kA[1] - tA) & (GE >= -kE[0] + tE) & (GE <= kE[1] - tE)
    outs = (GA < -kA[0] - tA) | (GA > kA[1] + tA) | (GE < -kE[0] - tE) | (GE > kE[1] + tE)
    out["p1c_nt_outside"] = int((nt & outs & inner).sum()); out["p1c_inside_trades"] = int((~nt & insd & inner).sum())
    out["p1c_nt"] = int((nt & inner).sum()); out["p1c_boundary_excluded"] = int((~insd & ~outs & inner).sum())
    return out


def figure_data(args):
    """Last-review fund edges against the ETF incumbent, for the figure."""
    corr, kA, kE, r, step, hfac = args
    S, cres, rho, hA, hE, sA, sE, dA, dE = grid(corr, kA, kE, step, hfac)
    YA, YE = np.meshgrid(dA, dE, indexing="ij")
    W = -0.5 * GAMMA * (S[0, 0] * YA ** 2 + 2 * S[0, 1] * YA * YE + S[1, 1] * YE ** 2)
    Z, AE = fastdp.l1(W, kE[0] * hE, kE[1] * hE, axis=1)
    U, AA = fastdp.l1(Z, kA[0] * hA, kA[1] * hA, axis=0)
    lo, hi, ok, _ = bands(AA == np.arange(len(dA))[:, None])
    return dict(corr=corr, kA=list(kA), kE=list(kE), dE=dE[ok].tolist(), lo=dA[lo[ok]].tolist(), hi=dA[hi[ok]].tolist(),
                cres=cres, rho=rho, SAA=S[0, 0], SAE=S[0, 1])


def main():
    t0 = time.time(); out = {}
    fund = [(0.001, 0.001), (0.005, 0.005)]; etf = [(0.0, 0.0), (0.0002, 0.0002), (0.001, 0.001), (0.005, 0.005)]
    cells = [(c, kA, kE, r, st, 1) for c in (0.0, 0.5, 0.9, 0.97) for kA in fund for kE in etf for r in (-0.8, 0.0, 0.8) for st in (0.5, 0.1)]
    cells += [(c, (0.01, 0.0), (0.0005, 0.0005), r, st, 1) for c in (0.0, 0.5, 0.9, 0.97) for r in (-0.8, 0.0, 0.8) for st in (0.5, 0.1)]
    cells += [(0.97, (0.001, 0.001), (0.001, 0.001), 0.0, 0.5, 2), (0.5, (0.005, 0.005), (0.0002, 0.0002), 0.8, 0.1, 2),
              (0.97, (0.01, 0.0), (0.0005, 0.0005), 0.0, 0.5, 2), (0.97, (0.01, 0.0), (0.0005, 0.0005), 0.0, 0.5, 4)]
    n036 = len(cells)
    cells += [(c, kA, kE, r, 0.5, 1) for c in (-0.5, -0.9) for kA in fund for kE in etf[1:] for r in (-0.8, 0.0, 0.8)]
    with mp.Pool(6) as pool:
        out["cells"] = pool.map(run_cell, cells, chunksize=1)
        out["figure"] = pool.map(figure_data, [(0.5, (0.001, 0.001), (0.001, 0.001), 0.0, 0.5, 1), (0.97, (0.001, 0.001), (0.001, 0.001), 0.0, 0.5, 1)])
    out["n036"] = n036; out["seconds"] = time.time() - t0
    out["statement"] = "claim 108 at c45de5a7 (approved; text as red-passed at 7c3f38e4)"
    out = json.loads(json.dumps(out, default=lambda o: o.tolist() if hasattr(o, "tolist") else (int(o) if isinstance(o, np.integer) else float(o))))
    json.dump(r036.rounded(out), open(HERE / "summary.json", "w"), separators=(",", ":"))
    print("done", out["seconds"])


if __name__ == "__main__":
    main()
