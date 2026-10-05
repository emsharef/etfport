"""Experiment 043 part 4: the ends of xi, by the two-instrument DP in the fine regime (average cost, relative value
iteration), with the ETF's and the fund's stationary idle probabilities. Run: uv run python experiments/043/run.py p4
"""
import json
import multiprocessing as mp
import time

import numpy as np

import run as R

GAMMA, SAA, SEE, fastdp = R.GAMMA, R.SAA, R.SEE, R.fastdp
KA = 0.002                              # fund round trip (10 bp each way)


def pad2(V, sA, sE, kA_h, kE_h):
    """Deviation 2 in two dimensions: beyond the grid the value falls at the trading rate of the instrument whose axis
    is left (exact where both bands lie inside the grid)."""
    a = np.arange(sA, 0, -1)[:, None]; e = np.arange(sE, 0, -1)[None, :]
    P = np.concatenate([V[:1] - kA_h * a, V, V[-1:] - kA_h * a[::-1]], 0)
    return np.concatenate([P[:, :1] - kE_h * e, P, P[:, -1:] - kE_h * e[:, ::-1]], 1)


def inputs(corr, xi, eps):
    SAE = corr * np.sqrt(SAA * SEE)
    rho_h, rho_p = SAE / SEE, SAE / SAA
    cres = GAMMA * (SAA - SAE ** 2 / SEE)
    Dfree = 3 * KA * eps ** 2 / (4 * cres)            # sqrt(v_A) = eps Delta_free
    u = eps * Dfree; vA = u ** 2
    vBeff = vA * (1 + rho_h ** 2)                      # v_B = v_A, r = 0
    kE = xi ** 3 * KA * GAMMA * SEE * vA / (vBeff * cres)
    DE = (3 * kE * vBeff / (4 * GAMMA * SEE)) ** (1 / 3)
    vid = vA * (1 + rho_p ** 2)
    Dfroz = (3 * KA * vid / (4 * GAMMA * SAA)) ** (1 / 3)
    return dict(SAE=SAE, rho_h=rho_h, rho_p=rho_p, cres=cres, Dfree=Dfree, u=u, kE=kE, DE=DE, Dfroz=Dfroz)


def cell(args):
    corr, xi, eps = args; t0 = time.time()
    I = inputs(corr, xi, eps); u = I["u"]; h = u / 4; s = 4
    S = np.array([[SAA, I["SAE"]], [I["SAE"], SEE]])
    big = max(I["Dfree"], I["Dfroz"])
    mA = int(np.ceil((max(3 * big, 1.2 * (I["Dfroz"] / (1 - corr ** 2) + abs(I["rho_p"]) * I["DE"])) + 10 * u) / h)); mE = int(np.ceil((1.5 * (I["DE"] + abs(I["rho_h"]) * 3 * big) + 10 * u) / h))
    dA = np.arange(-mA, mA + 1) * h; dE = np.arange(-mE, mE + 1) * h; nA, nE = len(dA), len(dE)
    YA, YE = np.meshgrid(dA, dE, indexing="ij")
    quad = -0.5 * GAMMA * (S[0, 0] * YA ** 2 + 2 * S[0, 1] * YA * YE + S[1, 1] * YE ** 2)
    kAh, kEh = KA / 2 * h, I["kE"] / 2 * h
    law = R.law4(0.0)
    n_stab = int(np.ceil(2 * (max(big, I["DE"]) / u) ** 2)); cap = 20000
    V = np.zeros_like(quad); g_hist = []; sig_last = None; stable = 0; conv = False
    jstar = np.clip(mE + np.round(-I["rho_h"] * dA / h).astype(int), 0, nE - 1)
    for it in range(1, cap + 1):
        P = pad2(V, s, s, KA / 2 * h, I["kE"] / 2 * h)
        W = quad + sum(pr * P[s - a * s: s - a * s + nA, s - e * s: s - e * s + nE] for (a, e), pr in law)
        Z, AE = fastdp.l1(W, kEh, kEh, axis=1)
        U, AA = fastdp.l1(Z, kAh, kAh, axis=0)
        g = U[mA, mE]; V = U - g; g_hist.append(g)
        if it % 25 == 0:
            nt = AA == np.arange(nA)[:, None]
            nt &= AE == np.arange(nE)[None, :]
            sec = np.nonzero(nt[np.arange(nA), jstar])[0]
            sig = (int(nt.sum()), int(sec.min()) if sec.size else -1, int(sec.max()) if sec.size else -1)
            stable = stable + 25 if sig == sig_last else 0; sig_last = sig
            if stable >= n_stab and it > n_stab and abs(g - g_hist[-1 - n_stab]) <= 1e-10 * abs(g):
                conv = True; break
    tol = 1e-12 * np.abs(W).max()
    fheld = Z - U >= -tol; eheld = W - Z >= -tol; ntv = U - W <= tol
    sec = np.nonzero(ntv[np.arange(nA), jstar])[0]
    half_e0 = (sec.max() - sec.min() + 1) / 2 * h if sec.size else None
    col = np.nonzero(fheld[:, mE])[0]                # Deviation 3: the fund's band at the ETF incumbent p^- = p*
    half = (col.max() - col.min() + 1) / 2 * h if col.size else None
    col_contig = bool(col.size and col.size == col.max() - col.min() + 1)
    col_room = int(min(col.min(), nA - 1 - col.max())) if col.size else None
    # the stationary law of the pre-trade deviation under the DP's policy (not simulated)
    ip = AA; jp = AE[ip, np.arange(nE)[None, :].repeat(nA, 0)]
    dest = (ip * nE + jp).ravel()
    fidle_m = (ip == np.arange(nA)[:, None]); eidle_m = (jp == np.arange(nE)[None, :])
    pi = ntv.astype(float); pi /= pi.sum(); leak = 0.0; tv = None
    n_pi = min(40000, 10 * n_stab)
    for k in range(n_pi):
        post = np.bincount(dest, weights=pi.ravel(), minlength=nA * nE).reshape(nA, nE)
        new = np.zeros_like(post)
        for (a, e), pr in law:                       # deviation moves by -(a, e) steps
            src = post[max(0, a * s): nA + min(0, a * s), max(0, e * s): nE + min(0, e * s)]
            new[max(0, -a * s): nA + min(0, -a * s), max(0, -e * s): nE + min(0, -e * s)] += pr * src
        tot = new.sum(); leak = 1 - tot; new = 0.5 * (pi + new / tot)      # the lazy chain: same stationary law, aperiodic
        if k % 100 == 0 or k == n_pi - 1:
            tv = 0.5 * np.abs(new - pi).sum()
        pi = new
    fid, eid = float((pi * fidle_m).sum()), float((pi * eidle_m).sum())
    # normalizers: one-instrument DPs at the same step (free end on this grid step; frozen end on u/40 with rounded jumps)
    free = R.rvi1(I["cres"], KA / 2, KA / 2, h, [(s, 0.5), (-s, 0.5)], mA + 4 * s, n_stab=int(np.ceil(2 * (I["Dfree"] / u) ** 2)))
    h2 = u / 40; kk = int(round(40 * I["rho_p"]))
    fz = R.rvi1(GAMMA * SAA, KA / 2, KA / 2, h2, [(a * 40 + e * kk, p) for (a, e), p in law], int(np.ceil((3 * big + 10 * u) / h2)) + 80,
                n_stab=int(np.ceil(2 * (I["Dfroz"] / u) ** 2)))
    return dict(corr=corr, xi=xi, eps=eps, nA=nA, nE=nE, iters=it, converged=conv, half=half, F=half / I["Dfree"] if half else None,
                col_contig=col_contig, col_room=col_room, F_e0=half_e0 / I["Dfree"] if half_e0 else None,
                e0_frozen_formula=I["Dfroz"] / (1 - corr ** 2) / I["Dfree"], e0_room=int(min(sec.min(), nA - 1 - sec.max())) if sec.size else None,
                free_end=(free["hi"] - free["lo"] + 1) / 2 * h / I["Dfree"], frozen_end=(fz["hi"] - fz["lo"] + 1) / 2 * h2 / I["Dfree"],
                frozen_end_formula=I["Dfroz"] / I["Dfree"], frozen_jump_rounding=abs(kk / 40 - I["rho_p"]), fund_idle=fid, etf_idle=eid,
                pi_iters=n_pi, pi_tv_last=tv, pi_leak=leak, gain_ratio_free=free["gain"], seconds=time.time() - t0, **I)


def main():
    t0 = time.time()
    cells = [(c, xi, e) for c in (0.5, 0.9) for xi in (0.25, 4.0) for e in (0.2, 0.1, 0.05)]
    cells.sort(key=lambda x: x[2])                   # the slowest first
    with mp.Pool(6) as pool:
        res = pool.map(cell, cells, chunksize=1)
    S_ = json.load(open(R.HERE / "summary.json")); S_["part4"] = json.loads(json.dumps(res, default=float)); S_["seconds_part4"] = time.time() - t0
    json.dump(R.r036.rounded(S_), open(R.HERE / "summary.json", "w"), separators=(",", ":"))
    print("done part 4", time.time() - t0)
