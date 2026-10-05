"""Experiment 043: claim 042 (the fund's fine-regime band with one costly ETF) against exact dynamic programs.
Registered design: experiments/043-claim042-fine-band-check.md.
Run: uv run python experiments/043/run.py        (parts 1-3)
     uv run python experiments/043/run.py p4     (part 4; adds to summary.json)

Solvers: experiment 036's two-instrument DP in deviation coordinates (fixed Sigma, beta = 1, no marking; exact L1
transforms from experiment 023's fastdp.l1), and one-instrument DPs on the same fund lattice. Held sets are read with
experiment 042's tie rule (staying attains the optimum within 1e-12 of the value scale).
"""
import importlib.util
import json
import multiprocessing as mp
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("run036", HERE.parent / "036" / "run.py")
r036 = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(r036)
fastdp = r036.fastdp
GAMMA, T, SAA, SEE, CAP = r036.GAMMA, r036.T, r036.SAA, r036.SEE, r036.CAP


class r042:
    """Experiment 042's two helpers (grid: 036's run_cell lines; bands: per-column held rows), copied so that 043 runs
    from main."""

    @staticmethod
    def grid(corr, kA, kE, step, hfac):
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

    @staticmethod
    def bands(held):
        any_ = held.any(0)
        lo = np.argmax(held, 0); hi = held.shape[0] - 1 - np.argmax(held[::-1], 0)
        contig = held.sum(0) == hi - lo + 1
        return lo, hi, any_ & contig, any_ & ~contig


def law4(r):
    return [((+1, +1), (1 + r) / 4), ((-1, -1), (1 + r) / 4), ((+1, -1), (1 - r) / 4), ((-1, +1), (1 - r) / 4)]


def shift1(V, shifts):
    """E V(y - k) over integer shifts k (grid units), edge-padded."""
    m = max(abs(k) for k, _ in shifts)
    P = np.pad(V, (m, m), mode="edge"); n = len(V)
    return sum(p * P[m - k: m - k + n] for k, p in shifts)


def shift1_lin(V, shifts, kp_h, km_h):
    """Deviation 2: E V(y - k), extended beyond the grid with slopes kappa^+ (below: buy back up) and kappa^- (above: sell
    back down), the exact value outside the band when the band lies inside the grid."""
    m = max(abs(k) for k, _ in shifts); n = len(V); ar = np.arange(m, 0, -1)
    P = np.concatenate([V[0] - kp_h * ar, V, V[-1] - km_h * ar[::-1]])
    return sum(p * P[m - k: m - k + n] for k, p in shifts)


def held1(W, kp, km, policy=False):
    U, A = fastdp.l1(W, kp, km, axis=0)
    tol = 1e-12 * np.abs(W).max()
    h = np.nonzero(U - W <= tol)[0]
    hb = (int(h.min()), int(h.max()), bool(h.size == h.max() - h.min() + 1))
    return (U, hb, A) if policy else (U, hb)


def idle1(A, shifts, n_it):
    """Deviation 5: the stationary probability that the instrument does not trade at a review, under the policy A
    (exact law of the lazy chain, iterated; not simulated). Returns (idle, last-step total variation)."""
    N = len(A); pi = np.full(N, 1.0 / N); tv = None
    for k in range(n_it):
        post = np.bincount(A, weights=pi, minlength=N)
        new = np.zeros(N)
        for d, p in shifts:                     # deviation moves by -d
            if d >= 0:
                new[: N - d] += p * post[d:]
            else:
                new[-d:] += p * post[: N + d]
        new = 0.5 * (pi + new / new.sum())
        if k == n_it - 1:
            tv = 0.5 * np.abs(new - pi).sum()
        pi = new
    return float(pi[A == np.arange(N)].sum()), float(tv)


def dp1(c, kp, km, y, shifts, T_):
    """Finite-horizon one-instrument DP; held (lo, hi, contiguous) per review t = 0..T-1."""
    V = np.zeros(len(y)); out = []
    for t in range(T_ - 1, -1, -1):
        W = -0.5 * c * y ** 2 + (shift1(V, shifts) if t < T_ - 1 else 0)
        V, hb = held1(W, kp, km); out.append(hb)
    return out[::-1]


def dp2(S, kA, kE, r, hA, hE, sA, sE, dA, dE, frozen=False):
    """Experiment 036's two-instrument DP; yields (t, W, Z, U, AA, AE) with Z = W for a frozen ETF."""
    YA, YE = np.meshgrid(dA, dE, indexing="ij"); nA, nE = len(dA), len(dE)
    quad = -0.5 * GAMMA * (S[0, 0] * YA ** 2 + 2 * S[0, 1] * YA * YE + S[1, 1] * YE ** 2)
    V = np.zeros_like(quad)
    for t in range(T - 1, -1, -1):
        cont = np.zeros_like(V)
        if t < T - 1:
            P = np.pad(V, ((sA, sA), (sE, sE)), mode="edge")
            for (a, e), pr in law4(r):
                cont += pr * P[sA - a * sA: sA - a * sA + nA, sE - e * sE: sE - e * sE + nE]
        W = quad + cont
        if frozen:
            Z, AE = W, None
        else:
            Z, AE = fastdp.l1(W, kE[0] * hE, kE[1] * hE, axis=1)
        U, AA = fastdp.l1(Z, kA[0] * hA, kA[1] * hA, axis=0)
        V = U
        yield t, W, Z, U, AA, AE


def fund_bands(Z, U):
    tol = 1e-12 * max(1.0, np.abs(Z).max())
    return r042.bands(Z - U >= -tol)


# ---------------------------------------------------------------- part 1
def part1():
    rng = np.random.default_rng([2043, 1]); res = []; cov = []
    for _ in range(1000):
        corr = rng.uniform(-0.99, 0.99); sa, se = np.exp(rng.uniform(np.log(0.05), np.log(0.5), 2)); g = rng.uniform(1, 10)
        S = np.array([[sa ** 2, corr * sa * se], [corr * sa * se, se ** 2]])
        ya, yb = rng.standard_normal(2) * 0.1
        rho_h = S[0, 1] / S[1, 1]; cres = g * (S[0, 0] - S[0, 1] ** 2 / S[1, 1]); e = yb + rho_h * ya
        lhs = 0.5 * g * np.array([ya, yb]) @ S @ np.array([ya, yb]); rhs = 0.5 * cres * ya ** 2 + 0.5 * g * S[1, 1] * e ** 2
        res.append(abs(lhs - rhs) / abs(lhs))
        # the innovation moments of (y_a, e) under the four-point law with steps uA, uB and correlation r
        uA, uB = np.exp(rng.uniform(np.log(1e-3), np.log(1e-1), 2)); r = rng.uniform(-1, 1)
        pts = [(-a * uA, -(b * uB) - rho_h * a * uA, p) for (a, b), p in law4(r)]      # (dy_a, de) = -(da*, db* + rho_h da*)
        m = lambda f: sum(p * f(x, z) for x, z, p in pts)
        vA, vBe, cv = m(lambda x, z: x * x), m(lambda x, z: z * z), m(lambda x, z: x * z)
        vB = uB ** 2
        cov.append(max(abs(vA - uA ** 2) / uA ** 2, abs(vBe - (vB + rho_h ** 2 * uA ** 2 + 2 * rho_h * r * uA * uB)) / vBe,
                       abs(cv - (r * uA * uB + rho_h * uA ** 2)) / max(abs(cv), uA * uB * 1e-3)))
        # control directions: a fund trade da moves (y_a, e) by (da, rho_h da); an ETF trade moves e only (linear, exact)
    return dict(identity_max=float(max(res)), moments_max=float(max(cov)))


# ---------------------------------------------------------------- part 2
def widen(dE, hE, sE):
    """Deviation 1: at least 20 interior ETF columns beyond 036's 3-step margin."""
    mE = (len(dE) - 1) // 2
    m2 = max(mE, 3 * sE + 20)
    return np.arange(-m2, m2 + 1) * hE


def part2ab(args):
    corr, kA, kE, r, step = args
    S, cres, rho, hA, hE, sA, sE, dA, dE = r042.grid(corr, kA, kE, step, 1)
    dE = widen(dE, hE, sE); nA, nE = len(dA), len(dE)
    c1 = GAMMA * SAA if corr == 0 else cres
    one = dp1(c1, kA[0] * hA, kA[1] * hA, dA, [(sA, 0.5), (-sA, 0.5)], T)
    colin = (np.arange(nE) > 3 * sE) & (np.arange(nE) < nE - 1 - 3 * sE)
    resA = hA + abs(S[0, 1]) * GAMMA * hE / cres
    rows = []
    for t, W, Z, U, AA, AE in dp2(S, kA, kE, r, hA, hE, sA, sE, dA, dE):
        lo, hi, ok, nc = fund_bands(Z, U)
        use = ok & colin & (lo > 3 * sA) & (hi < nA - 1 - 3 * sA)
        l1, h1, c1ok = one[t]
        d = np.maximum(np.abs(lo[use] - l1), np.abs(hi[use] - h1))
        rows.append(dict(t=t, cols=int(use.sum()), noncontig=int((nc & colin).sum()), diff_steps=int(d.max()) if d.size else None,
                         diff_res=float(d.max() * hA / resA) if d.size else None,
                         range_steps=int(max(np.ptp(lo[use]), np.ptp(hi[use]))) if d.size else None, one_contig=c1ok))
    return dict(corr=corr, kA=list(kA), kE=list(kE), r=r, step=step, hA=hA, resA=resA, kind="a" if corr == 0 else "b", rows=rows[::-1])


def part2c(args):
    corr, kA, r, step = args
    SAE = corr * np.sqrt(SAA * SEE); S = np.array([[SAA, SAE], [SAE, SEE]])
    rp = SAE / SAA; sg = int(np.sign(rp))
    wA0 = (kA[0] + kA[1]) / (GAMMA * SAA); hA = wA0 / 100; sA = max(1, round(step * wA0 / hA)); hE = hA / abs(rp); sE = sA
    mE = (T + 2) * sE + 20; mA = mE + int(np.ceil(wA0 / hA)) + (T + 4) * sA
    dA = np.arange(-mA, mA + 1) * hA; dE = np.arange(-mE, mE + 1) * hE; nA, nE = len(dA), len(dE)
    shifts = [(a * sA + sg * e * sA, p) for (a, e), p in law4(r)]
    one = dp1(GAMMA * SAA, kA[0] * hA, kA[1] * hA, dA, shifts, T)      # y-lattice = fund lattice (index i - sg (j - mE))
    vid_law = sum(p * ((a * sA + sg * e * sA) * hA) ** 2 for (a, e), p in law4(r))
    uA = sA * hA; uE = sE * hE; vid_f = uA ** 2 + rp ** 2 * uE ** 2 + 2 * rp * r * uA * uE
    rows = []
    for t, W, Z, U, AA, AE in dp2(S, kA, (np.inf, np.inf), r, hA, hE, sA, sE, dA, dE, frozen=True):
        lo, hi, ok, nc = fund_bands(Z, U)
        j = np.arange(nE); margin = (T - t + 1) * sE
        use = ok & (j > margin) & (j < nE - 1 - margin) & (lo > (T - t + 4) * sA) & (hi < nA - 1 - (T - t + 4) * sA)
        l1, h1, c1ok = one[t]
        plo = l1 - sg * (j - mE); phi = h1 - sg * (j - mE)
        d = np.maximum(np.abs(lo - plo), np.abs(hi - phi))[use]
        w = (hi - lo)[use] * hA
        rows.append(dict(t=t, cols=int(use.sum()), diff_steps=int(d.max()) if d.size else None, width_over_ceiling=float(w.max() / wA0) if w.size else None))
    return dict(corr=corr, kA=list(kA), r=r, step=step, rho_prime=rp, v_idle_law=vid_law, v_idle_formula=vid_f, hA=hA, rows=rows[::-1])


# ---------------------------------------------------------------- part 3
def rvi1(c, kp, km, h, shifts, n, n_stab, cap=200000):
    """Average-cost relative value iteration on y = (-n..n) h; held set, gain, iterations."""
    y = np.arange(-n, n + 1) * h; V = np.zeros(len(y)); g_hist = []; last = None; stable = 0
    for it in range(1, cap + 1):
        W = -0.5 * c * y ** 2 + shift1_lin(V, shifts, kp * h, km * h)
        U, hb, A = held1(W, kp * h, km * h, policy=True)
        g = U[n]; V = U - g; g_hist.append(g)
        stable = stable + 1 if hb == last else 0; last = hb
        if stable >= n_stab and it > n_stab and abs(g - g_hist[-1 - n_stab]) <= 1e-10 * abs(g):
            return dict(lo=hb[0] - n, hi=hb[1] - n, contig=hb[2], gain=-g, iters=it, converged=True, A=A)
    return dict(lo=last[0] - n, hi=last[1] - n, contig=last[2], gain=-g_hist[-1], iters=cap, converged=False, A=A)


def part3(args):
    kind, corr, kA, r, eps = args
    SAE = corr * np.sqrt(SAA * SEE)
    if kind == "a":
        c = GAMMA * SAA
    elif kind == "b":
        c = GAMMA * (SAA - SAE ** 2 / SEE)
    else:
        c = GAMMA * SAA
    ks = kA[0] + kA[1]
    # the lattice: v is set from eps through Delta^3 = 3 ks v / (4c) and sqrt(v) = eps Delta, so Delta = 3 ks eps^2/(4c)
    Delta = 3 * ks * eps ** 2 / (4 * c); sd = eps * Delta
    if kind in ("a", "b"):
        u = sd; h = u / 20; k = 20; shifts = [(k, 0.5), (-k, 0.5)]
    else:                                  # idle target: steps (+-1 +- 1) u_A with |rho'| u_E = u_A; v = 2 u_A^2 (1 + r)
        rsg = r * np.sign(SAE / SAA)
        u = sd / np.sqrt(2 * (1 + rsg)); h = u / 20; k = 20
        shifts = [(2 * k, (1 + rsg) / 4), (-2 * k, (1 + rsg) / 4), (0, (1 - rsg) / 2)]
    v = sum(p * (s * h) ** 2 for s, p in shifts)
    n = int(np.ceil((3 * Delta + 10 * u) / h)) + 2 * max(abs(s) for s, _ in shifts)
    out = rvi1(c, kA[0], kA[1], h, shifts, n, n_stab=int(np.ceil(2 * (Delta / u) ** 2)))
    half = (out["hi"] - out["lo"] + 1) / 2 * h; centre = (out["hi"] + out["lo"]) / 2 * h
    idle, tv = idle1(out["A"], shifts, min(400000, 20 * int(np.ceil(2 * (Delta / u) ** 2))))
    return dict(kind=kind, corr=corr, kA=list(kA), r=r, eps=eps, c=c, v=v, Delta=Delta, h=h, half=half, ratio=half / Delta,
                centre_over_Delta=centre / Delta, gain_ratio=out["gain"] / (c * Delta ** 2 / 2), iters=out["iters"], converged=out["converged"],
                contig=out["contig"], edge_room=int(n - max(abs(out["lo"]), abs(out["hi"]))), idle=idle, idle_tv=tv)


def main3():
    """Part 3 alone (rerun after Deviation 2)."""
    t0 = time.time(); EPS = (0.2, 0.1, 0.05, 0.02, 0.01)
    p3 = [("a", 0.0, kA, 0.0, e) for kA in [(0.001, 0.001), (0.005, 0.005), (0.01, 0.0)] for e in EPS]
    p3 += [("b", c, kA, 0.0, e) for c in (0.5, 0.97) for kA in [(0.001, 0.001), (0.005, 0.005), (0.01, 0.0)] for e in EPS]
    p3 += [("c", c, kA, r, e) for c in (0.5, 0.97) for kA in [(0.001, 0.001), (0.005, 0.005)] for r in (-0.8, 0.0, 0.8) for e in EPS]
    with mp.Pool(4) as pool:
        res = pool.map(part3, p3, chunksize=1)
    S_ = json.load(open(HERE / "summary.json")); S_["part3"] = json.loads(json.dumps(res, default=float)); S_["seconds_part3"] = time.time() - t0
    json.dump(r036.rounded(S_), open(HERE / "summary.json", "w"), separators=(",", ":"))
    print("done part 3", time.time() - t0)


def main():
    t0 = time.time(); S_ = dict(statement="claim 042 on main at f7d6b394 (Statement of abd716ad, red-passed conditionally); revision f74f30be on math/claim042-revision-text")
    S_["part1"] = part1()
    fund = [(0.001, 0.001), (0.005, 0.005)]; etf = [(0.0, 0.0), (0.0002, 0.0002), (0.001, 0.001), (0.005, 0.005)]
    ab = [(0.0, kA, kE, r, st) for kA in fund for kE in etf for r in (-0.8, 0.0, 0.8) for st in (0.5, 0.1)]
    ab += [(0.0, (0.01, 0.0), (0.0005, 0.0005), r, st) for r in (-0.8, 0.0, 0.8) for st in (0.5, 0.1)]
    ab += [(c, kA, (0.0, 0.0), r, st) for c in (0.5, 0.9, 0.97) for kA in fund for r in (-0.8, 0.0, 0.8) for st in (0.5, 0.1)]
    cc = [(c, kA, r, st) for c in (0.5, 0.9, 0.97, -0.5) for kA in fund for r in (-0.8, 0.0, 0.8) for st in (0.5, 0.1)]
    EPS = (0.2, 0.1, 0.05, 0.02, 0.01)
    p3 = [("a", 0.0, kA, 0.0, e) for kA in [(0.001, 0.001), (0.005, 0.005), (0.01, 0.0)] for e in EPS]
    p3 += [("b", c, kA, 0.0, e) for c in (0.5, 0.97) for kA in [(0.001, 0.001), (0.005, 0.005), (0.01, 0.0)] for e in EPS]
    p3 += [("c", c, kA, r, e) for c in (0.5, 0.97) for kA in [(0.001, 0.001), (0.005, 0.005)] for r in (-0.8, 0.0, 0.8) for e in EPS]
    with mp.Pool(8) as pool:
        S_["part3"] = pool.map_async(part3, p3, chunksize=1)
        S_["part2ab"] = pool.map(part2ab, ab, chunksize=1); print("2ab", time.time() - t0, flush=True)
        S_["part2c"] = pool.map(part2c, cc, chunksize=1); print("2c", time.time() - t0, flush=True)
        S_["part3"] = S_["part3"].get(); print("3", time.time() - t0, flush=True)
    S_["seconds"] = time.time() - t0
    S_ = json.loads(json.dumps(S_, default=lambda o: o.tolist() if hasattr(o, "tolist") else (int(o) if isinstance(o, np.integer) else float(o))))
    old = json.load(open(HERE / "summary.json")) if (HERE / "summary.json").exists() else {}
    old.update(S_)
    json.dump(r036.rounded(old), open(HERE / "summary.json", "w"), separators=(",", ":"))
    print("done", S_["seconds"])


if __name__ == "__main__":
    if sys.argv[1:] == ["p3"]:
        main3()
    elif sys.argv[1:] == ["p4"]:
        import p4
        p4.main()
    else:
        main()
