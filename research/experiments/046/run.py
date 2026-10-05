"""Experiment 046: claim 043 (the sandwich on the pair's fine-regime cost; math/claim043-d15e-sandwich-text 44df90f8)
against experiment 043's two-instrument lattice DP, which here records its gain (average cost per review).
Registered design: experiments/046-claim043-sandwich-check.md.  Run: uv run python experiments/046/run.py
"""
import importlib.util
import json
import multiprocessing as mp
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
_s43 = importlib.util.spec_from_file_location("run043", HERE.parent / "043" / "run.py")
R43 = importlib.util.module_from_spec(_s43); _s43.loader.exec_module(R43)      # experiment 043's run.py: rvi1, law4, fastdp
_saved = sys.modules.get("run"); sys.modules["run"] = R43                       # 043's p4.py imports it as "run"
_spec = importlib.util.spec_from_file_location("p4_043", HERE.parent / "043" / "p4.py")
P4 = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(P4)
if _saved is None:
    del sys.modules["run"]
else:
    sys.modules["run"] = _saved
GAMMA, SAA, SEE, fastdp = R43.GAMMA, R43.SAA, R43.SEE, R43.fastdp
KA_SIDE = 0.001                                         # experiment 043's fund rate per side (KA = 0.002 round trip)


def inputs(corr, xi, eps, r):
    """043's part 4 inputs, with the innovation correlation r (v_B = v_A)."""
    SAE = corr * np.sqrt(SAA * SEE); rho_h = SAE / SEE
    cres = GAMMA * (SAA - SAE ** 2 / SEE); cE = GAMMA * SEE
    Dfree = 3 * 2 * KA_SIDE * eps ** 2 / (4 * cres); u = eps * Dfree; vA = vB = u ** 2
    vBeff = vB + rho_h ** 2 * vA + 2 * rho_h * r * np.sqrt(vA * vB)
    kE_rt = xi ** 3 * 2 * KA_SIDE * cE * vA / (vBeff * cres)           # xi^3 = (kE/kA)(vBeff/vA)(cres/cE), round trips
    return dict(SAE=SAE, rho_h=rho_h, cres=cres, cE=cE, u=u, vA=vA, vB=vB, vBeff=vBeff, kA=KA_SIDE, kE=kE_rt / 2, Dfree=Dfree,
                DE=(3 * kE_rt * vBeff / (4 * cE)) ** (1 / 3), Dfroz=(3 * 2 * KA_SIDE * (vA + (SAE / SAA) ** 2 * vB + 2 * SAE / SAA * r * u * u) / (4 * GAMMA * SAA)) ** (1 / 3))


def bounds(I):
    """Claim 043's bounds, per-side rates k (AX-15's eigenvalue a(k) = (c/2)(3 (2k) v/(4c))^(2/3))."""
    a = lambda c, k, v: 0.5 * c * (3 * 2 * max(k, 0.0) * v / (4 * c)) ** (2 / 3)
    aA = lambda k: a(I["cres"], k, I["vA"]); aE = lambda k: a(I["cE"], k, I["vBeff"])
    rh, kA, kE = abs(I["rho_h"]), I["kA"], I["kE"]
    x = rh * kE / kA
    up = aA(kA + rh * kE) + aE(kE)
    lo_disp = aA(kA - rh * kE) + aE(kE) if x < 1 else None
    # the general lower bound: max over kE' in [0, min(kE, kA/rh)] of aA(kA - rh kE') + aE(kE') (the constraint binds at the max)
    kmax = min(kE, kA / rh) if rh > 0 else kE
    grid = np.unique(np.concatenate([np.linspace(0, kmax, 2001), [0.0, kmax]]))
    vals = [(aA(kA - rh * k) + aE(k), k) for k in grid]; lo_gen, kbest = max(vals)
    gen_A, gen_E = aA(kA - rh * kbest), aE(kbest)
    cb = I["cres"] * I["cE"] / (I["cres"] + I["rho_h"] ** 2 * I["cE"])
    lo_b = a(cb, kE, I["vB"])
    dec = aA(kA) + aE(kE)
    gap_id = ((1 + x) ** (2 / 3) - (1 - x) ** (2 / 3)) if x < 1 else None
    gap_meas = (up - lo_disp) / aA(kA) if lo_disp is not None else None
    return dict(x=x, up=up, lo_disp=lo_disp, lo_gen=lo_gen, lo_b=lo_b, dec=dec, aA=aA(kA), aE=aE(kE), aA_up=aA(kA + rh * kE),
                aA_lo=aA(kA - rh * kE) if x < 1 else None, gen_A=gen_A, gen_E=gen_E, aE_gen_k=float(kbest),
                gap_err=abs(gap_id - gap_meas) if gap_id is not None else None, gap_bound_ok=bool(gap_id <= 2 * (1 - (1 - x) ** (2 / 3)) + 1e-15) if gap_id is not None else None)


def gain2(I, r, cap=20000):
    """043's two-instrument average-cost relative value iteration (grid u/4, linear extension beyond the grid); the gain."""
    corr_S = np.array([[SAA, I["SAE"]], [I["SAE"], SEE]]); u = I["u"]; h = u / 4; s = 4
    big = max(I["Dfree"], I["Dfroz"])
    mA = int(np.ceil((max(3 * big, 1.2 * (I["Dfroz"] + abs(I["SAE"] / SAA) * I["DE"])) + 10 * u) / h))
    mE = int(np.ceil((1.5 * (I["DE"] + abs(I["rho_h"]) * 3 * big) + 10 * u) / h))
    dA = np.arange(-mA, mA + 1) * h; dE = np.arange(-mE, mE + 1) * h; nA, nE = len(dA), len(dE)
    YA, YE = np.meshgrid(dA, dE, indexing="ij")
    quad = -0.5 * GAMMA * (corr_S[0, 0] * YA ** 2 + 2 * corr_S[0, 1] * YA * YE + corr_S[1, 1] * YE ** 2)
    kAh, kEh = I["kA"] * h, I["kE"] * h
    law = R43.law4(r)
    n_stab = int(np.ceil(2 * (max(big, I["DE"]) / u) ** 2))
    V = np.zeros_like(quad); g_hist = []; last = None; stable = 0; conv = False
    for it in range(1, cap + 1):
        P = P4.pad2(V, s, s, kAh, kEh)
        W = quad + sum(pr * P[s - a * s: s - a * s + nA, s - e * s: s - e * s + nE] for (a, e), pr in law)
        Z, AE = fastdp.l1(W, kEh, kEh, axis=1)
        U, AA = fastdp.l1(Z, kAh, kAh, axis=0)
        g = U[mA, mE]; V = U - g; g_hist.append(g)
        if it % 25 == 0:
            sig = int(((AA == np.arange(nA)[:, None]) & (AE == np.arange(nE)[None, :])).sum())
            stable = stable + 25 if sig == last else 0; last = sig
            if stable >= n_stab and it > n_stab and abs(g - g_hist[-1 - n_stab]) <= 1e-10 * abs(g):
                conv = True; break
    drift = abs(g_hist[-1] - g_hist[-min(len(g_hist), 1000)]) / abs(g_hist[-1])
    return -g_hist[-1], it, conv, drift, (nA, nE)


def one_ratios(I, r, eps):
    """One-instrument gain ratios at the same step (043's rvi1): the fund (c^res, +-u walk, grid u/4) and the ETF (c_E, the
    effective target e's four-point law, jumps rounded to u/40)."""
    u = I["u"]; h = u / 4
    b = bounds(I)
    fa = R43.rvi1(I["cres"], I["kA"], I["kA"], h, [(4, 0.5), (-4, 0.5)], int(np.ceil((3 * I["Dfree"] + 10 * u) / h)) + 8,
                  n_stab=int(np.ceil(2 * (I["Dfree"] / u) ** 2)))
    rA = fa["gain"] / b["aA"]
    rh = I["rho_h"]; h2 = u / 40
    sh = [(int(round(40 * (e + rh * a))), p) for (a, e), p in R43.law4(r)]
    DE = I["DE"]
    fe = R43.rvi1(I["cE"], I["kE"], I["kE"], h2, sh, int(np.ceil((3 * DE + 10 * u * (1 + abs(rh))) / h2)) + 2 * max(abs(k) for k, _ in sh),
                  n_stab=int(np.ceil(2 * (DE / (u * np.sqrt(1 + rh ** 2))) ** 2)), cap=200000)
    rE = fe["gain"] / b["aE"]
    return rA, rE, fa["converged"], fe["converged"], abs(40 * rh - round(40 * rh)) / 40


def cell(args):
    corr, xi, eps, r, part = args; t0 = time.time()
    I = inputs(corr, xi, eps, r); b = bounds(I)
    a, it, conv, drift, shape = gain2(I, r)
    rA, rE, cA, cE_, rnd = one_ratios(I, r, eps)
    return dict(part=part, corr=corr, xi=xi, eps=eps, r=r, a=a, iters=it, converged=conv, drift=drift, grid=shape, rA=rA, rE=rE, convA=cA, convE=cE_,
                jump_round=rnd, epsE=float(I["u"] * np.sqrt(1 + I["rho_h"] ** 2) / I["DE"]), seconds=time.time() - t0, **b,
                **{k: I[k] for k in ("rho_h", "kA", "kE", "cres", "cE")})


def main():
    t0 = time.time()
    cells = [(c, xi, e, 0.0, "1") for c in (0.5, 0.9) for xi in (0.25, 4.0) for e in (0.2, 0.1, 0.05)]
    cells += [(0.0, xi, e, r, "2") for xi in (0.25, 4.0) for e in (0.2, 0.1) for r in (0.0, 0.8)]
    cells += [(0.9, xi, 0.2, 0.0, "4c") for xi in (0.25, 1.0, 4.0, 8.0)]
    cells.sort(key=lambda c: (c[2], -c[1]))            # the slowest first
    with mp.Pool(6) as pool:
        res = pool.map(cell, cells, chunksize=1)
    S = dict(cells=res, seconds=time.time() - t0, statement="claim 043 at 44df90f8 (math/claim043-d15e-sandwich-text; bounds unchanged since 5cb1e1e7)")
    json.dump(S, open(HERE / "summary.json", "w"), separators=(",", ":"), default=lambda o: o.tolist() if hasattr(o, "tolist") else (int(o) if isinstance(o, np.integer) else float(o)))
    print("done", S["seconds"])


if __name__ == "__main__":
    main()
