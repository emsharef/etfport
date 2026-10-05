"""Grid checks of claim 107 (M7, one fund and one ETF, finite tree, pure-learning marking).

Two-instrument backward induction on a holdings grid; the fund's effective band is read from the
full optimum's fund trade at every (fund incumbent, ETF incumbent). Tolerances are a few grid
cells. All inputs are assumed. A check, not a proof. Run: uv run python checks/107/check.py
"""
import sys
import numpy as np

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


def run(name, corr, kpE, kmE, T=3):
    gamma = 5.0
    sA2, sE2 = 0.012, 0.0073                      # fund and ETF variances
    SAE = corr * np.sqrt(sA2 * sE2)
    Sig = np.array([[sA2, SAE], [SAE, sE2]])
    rho = SAE / sE2
    s_res = sA2 - SAE * SAE / sE2
    cres = gamma * s_res
    kpA = kmA = 0.01
    beta = 1.0
    # targets on a tree: two outcomes per step, moving both targets
    a0, p0 = 0.45, 0.9
    moves = [(+0.05, +0.06), (-0.05, -0.06)]
    # grids
    da, dp = 0.01, 0.02
    A = np.round(np.arange(0.0, 1.0 + da / 2, da), 12)
    P = np.round(np.arange(0.0, 2.2 + dp / 2, dp), 12)
    NA, NP = len(A), len(P)
    AA, PP = np.meshgrid(A, P, indexing="ij")
    X = np.stack([AA.ravel(), PP.ravel()], axis=1)           # states = actions
    n = len(X)
    # cost matrix pieces (state -> action), fund and ETF separately
    dA_ = A[None, :] - A[:, None]; costA = kpA * np.maximum(dA_, 0) + kmA * np.maximum(-dA_, 0)
    dP_ = P[None, :] - P[:, None]; costE = kpE * np.maximum(dP_, 0) + kmE * np.maximum(-dP_, 0)

    def nodes(t):
        # all histories of length t: targets after t moves
        out = []
        for h in np.ndindex(*([2] * t)):
            a, p = a0, p0
            for k in h:
                a += moves[k][0]; p += moves[k][1]
            out.append((h, a, p))
        return out

    V = {h: np.zeros(n) for (h, _, _) in nodes(T)}
    results = []
    for t in range(T - 1, -1, -1):
        Vt = {}
        for (h, at, pt) in nodes(t):
            d = X - np.array([at, pt])
            G = 0.5 * gamma * np.einsum("ij,jk,ik->i", d, Sig, d)
            if t < T - 1:
                G = G + beta * 0.5 * (V[h + (0,)] + V[h + (1,)])
            # full optimum from every state: min over actions of costA + costE + G
            # tot[state, action] = costA[ia, ia'] + costE[ip, ip'] + G[action]
            tot = (costA[:, None, :, None] + costE[None, :, None, :]).reshape(n, n) + G[None, :]
            arg = np.argmin(tot, axis=1)
            Vt[h] = tot[np.arange(n), arg]
            post = X[arg]
            # fund trade from every state, grouped by ETF incumbent
            fa = post[:, 0].reshape(NA, NP); fp = post[:, 1].reshape(NA, NP)
            for ip in range(NP):
                held = np.where(np.abs(fa[:, ip] - A) < 1e-12)[0]
                if len(held) == 0:
                    continue
                lo, hi = A[held.min()], A[held.max()]
                clip = np.minimum(np.maximum(A, lo), hi)
                check(np.max(np.abs(fa[:, ip] - clip)) <= da + 1e-12, f"{name}: fund trade not a clip at t={t} node={h} ETF={P[ip]:.2f}")
                check(hi - lo <= (kpA + kmA) / cres + 2 * da + 1e-12, f"{name}: width {hi-lo:.3f} above residual static width {(kpA+kmA)/cres:.3f} at t={t} node={h} ETF={P[ip]:.2f}")
                # outer bracket (1c), when edges interior and ETF optimizer interior at the edges
                Hp = max(rho, 0) * (kpE + beta * kmE) + max(-rho, 0) * (kmE + beta * kpE) if t < T - 1 else max(rho, 0) * kpE + max(-rho, 0) * kmE
                Hm = max(rho, 0) * (kmE + beta * kpE) + max(-rho, 0) * (kpE + beta * kmE) if t < T - 1 else max(rho, 0) * kmE + max(-rho, 0) * kpE
                bA = beta if t < T - 1 else 0.0
                interior = 0 < lo and hi < A[-1]
                etf_int = all(1e-9 < fp[i, ip] < P[-1] - 1e-9 for i in (held.min(), held.max()))
                if interior and etf_int:
                    check(hi <= at + (kmA + bA * kpA + Hp) / cres + 2 * da, f"{name}: upper edge {hi:.3f} above bracket at t={t} node={h} ETF={P[ip]:.2f}")
                    check(lo >= at - (kpA + bA * kmA + Hm) / cres - 2 * da, f"{name}: lower edge {lo:.3f} below bracket at t={t} node={h} ETF={P[ip]:.2f}")
                # outer parallelotope (part 2) for held points that also hold the ETF
                both = [i for i in held if abs(fp[i, ip] - P[ip]) < 1e-12]
                for i in both:
                    dd = np.array([A[i] - at, P[ip] - pt])
                    m = gamma * Sig @ dd
                    lim_lo = np.array([-(kpA + bA * kmA), -(kpE + bA * kmE)]); lim_hi = np.array([kmA + bA * kpA, kmE + bA * kpE])
                    tol = gamma * np.abs(Sig).sum(axis=1) * max(da, dp) * 1.5
                    check(np.all(m >= lim_lo - tol) and np.all(m <= lim_hi + tol), f"{name}: no-trade point outside the outer parallelotope at t={t}")
                results.append((t, h, P[ip], lo, hi))
        V = Vt
    widths = [hi - lo for (_, _, _, lo, hi) in results]
    print(f"{name}: ok  (corr {corr}, rho {rho:.3f}, residual static width {(kpA+kmA)/cres:.3f}; bands {len(results)}, width range {min(widths):.3f}-{max(widths):.3f})")
    return results, cres, rho


r1, cres1, _ = run("frictionless ETF, corr 0.8", 0.8, 0.0, 0.0)
# part 3: with a frictionless ETF the fund band is independent of the ETF incumbent, and equals a 1-D DP of the reduced problem
by_node = {}
for (t, h, pinc, lo, hi) in r1:
    by_node.setdefault((t, h), []).append((lo, hi))
for key, bands in by_node.items():
    los = [b[0] for b in bands]; his = [b[1] for b in bands]
    check(max(los) - min(los) <= 0.01 + 1e-12 and max(his) - min(his) <= 0.01 + 1e-12, f"part 3: fund band varies with the ETF incumbent at {key}")
# 1-D reduced DP for comparison (same tree, curvature cres, target a)
gamma = 5.0; kpA = kmA = 0.01; da = 0.01
A = np.round(np.arange(0.0, 1.0 + da / 2, da), 12)
dA_ = A[None, :] - A[:, None]; costA = kpA * np.maximum(dA_, 0) + kmA * np.maximum(-dA_, 0)
moves = [+0.05, -0.05]; a0 = 0.45; T = 3
def nodes1(t):
    out = []
    for h in np.ndindex(*([2] * t)):
        a = a0 + sum(moves[k] for k in h); out.append((h, a))
    return out
V = {h: np.zeros(len(A)) for (h, _) in nodes1(T)}
bands1 = {}
for t in range(T - 1, -1, -1):
    Vt = {}
    for (h, at) in nodes1(t):
        G = 0.5 * cres1 * (A - at) ** 2
        if t < T - 1:
            G = G + 0.5 * (V[h + (0,)] + V[h + (1,)])
        tot = costA + G[None, :]; arg = np.argmin(tot, axis=1); Vt[h] = tot[np.arange(len(A)), arg]
        held = np.where(arg == np.arange(len(A)))[0]; bands1[(t, h)] = (A[held.min()], A[held.max()])
    V = Vt
for key, bands in by_node.items():
    lo1, hi1 = bands1[key]
    lo2, hi2 = bands[0]
    check(abs(lo1 - lo2) <= 0.02 + 1e-12 and abs(hi1 - hi2) <= 0.02 + 1e-12, f"part 3: two-instrument band ({lo2:.2f},{hi2:.2f}) differs from the reduced 1-D band ({lo1:.2f},{hi1:.2f}) at {key}")
print("part 3: ok  (frictionless ETF: fund band independent of the ETF incumbent and equal to the reduced one-instrument band)")

run("costly ETF 20 bp, corr 0.8", 0.8, 0.002, 0.002)
run("costly ETF 20 bp, corr 0.3", 0.3, 0.002, 0.002)

if FAIL:
    print(f"{len(FAIL)} check(s) failed"); sys.exit(1)
print("all checks passed")
