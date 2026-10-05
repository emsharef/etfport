"""Grid checks of claim 108 (M7, one fund and one ETF, finite tree, pure-learning marking): the
dynamic shape of the bundling band.

Two-instrument backward induction on a holdings grid, with the ETF-optimized value U_t(a; p^-)
computed by a two-pass minimization (ETF pass, then fund pass). Checks: part 1's exact
last-review edge functions of the ETF incumbent (medians of the idle line and the two re-hedge
levels; the bend's length is the ETF's residual static width); part 2's monotonicity of the fund's
edges in the ETF incumbent, and of the ETF's edges in the fund holding, with the sign of Sigma_AE,
at every review and node; part 3's frozen-ETF limit against a one-instrument dynamic program with
the idle-ETF target; part 4's r-free last review. The slope observation of Not shown is printed.
Tolerances are a grid step or two. All inputs are assumed. A check, not a proof.
Run: uv run python checks/108/check.py
"""
import sys
import numpy as np

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


def median3(x, y, z):
    return np.maximum(np.minimum(x, y), np.minimum(np.maximum(x, y), z))


def make(corr, kpE, kmE, kpA=0.01, kmA=0.01, gamma=5.0, sA2=0.012, sE2=0.0073, da=0.005, dp=0.01):
    SAE = corr * np.sqrt(sA2 * sE2)
    d = dict(gamma=gamma, Sig=np.array([[sA2, SAE], [SAE, sE2]]), SAE=SAE, sA2=sA2, sE2=sE2,
             rho=SAE / sE2, rhoA=SAE / sA2, cres=gamma * (sA2 - SAE * SAE / sE2), cresE=gamma * (sE2 - SAE * SAE / sA2),
             kpA=kpA, kmA=kmA, kpE=kpE, kmE=kmE, da=da, dp=dp)
    d["A"] = np.round(np.arange(0.0, 1.0 + da / 2, da), 12)
    d["P"] = np.round(np.arange(0.0, 2.4 + dp / 2, dp), 12)
    A, P = d["A"], d["P"]
    dA_ = A[None, :] - A[:, None]; d["costA"] = kpA * np.maximum(dA_, 0) + kmA * np.maximum(-dA_, 0)
    dP_ = P[None, :] - P[:, None]; d["costE"] = kpE * np.maximum(dP_, 0) + kmE * np.maximum(-dP_, 0)
    return d


def stay(d, at, pt, cont=None):
    """G_t on the grid: quadratic loss around the targets plus the continuation (NA x NP)."""
    A, P = d["A"], d["P"]
    da_ = (A - at)[:, None]; dp_ = (P - pt)[None, :]
    G = 0.5 * d["gamma"] * (d["sA2"] * da_ ** 2 + 2 * d["SAE"] * da_ * dp_ + d["sE2"] * dp_ ** 2)
    return G if cont is None else G + cont


def step(d, G, frozen=False):
    """One review: returns V (NA x NP over pre-trade states), the post-trade fund and ETF holdings
    (indices), and U = the ETF-optimized value U_t(a; p^-) (NA x NP). frozen: the ETF cannot trade."""
    NA, NP = G.shape
    if frozen:
        U = G.copy(); pE = np.tile(np.arange(NP), (NA, 1))
    else:
        # U[a', p] = min_{p'} costE[p, p'] + G[a', p'];  costE[p, p'] indexed (pre, post)
        tot = d["costE"][None, :, :] + G[:, None, :]        # (a', p, p')
        pE = np.argmin(tot, axis=2); U = np.take_along_axis(tot, pE[:, :, None], axis=2)[:, :, 0]
    # V[a, p] = min_{a'} costA[a, a'] + U[a', p]
    tot2 = d["costA"][:, :, None] + U[None, :, :]           # (a, a', p)
    aA = np.argmin(tot2, axis=1); V = np.take_along_axis(tot2, aA[:, None, :], axis=1)[:, 0, :]
    # post-trade ETF index at the chosen fund holding: pE[a'(a,p), p]
    pPost = pE[aA, np.arange(NP)[None, :]]
    return V, aA, pPost, U


def tree(T, a0, p0, moves, weights=None):
    """Targets on a finite tree; moves: list of (da*, dp*) per branch, equal weights unless given."""
    k = len(moves)
    w = np.full(k, 1.0 / k) if weights is None else np.asarray(weights)

    def nodes(t):
        out = []
        for h in np.ndindex(*([k] * t)):
            a, p = a0, p0
            for b in h:
                a += moves[b][0]; p += moves[b][1]
            out.append((h, a, p))
        return out
    return nodes, w


def bands_from_post(d, aA, pPost):
    """Fund band per ETF incumbent (columns) and ETF band per fund holding (rows), grid indices."""
    NA, NP = aA.shape
    ia = np.arange(NA)[:, None]
    heldA = (aA == ia)                                    # fund held at (a, p)
    lo = np.array([d["A"][np.where(heldA[:, j])[0].min()] if heldA[:, j].any() else np.nan for j in range(NP)])
    hi = np.array([d["A"][np.where(heldA[:, j])[0].max()] if heldA[:, j].any() else np.nan for j in range(NP)])
    return lo, hi, heldA


def run(name, corr, kpE, kmE, T=3, moves=((+0.05, +0.06), (-0.05, -0.06)), weights=None, a0=0.45, p0=1.0):
    d = make(corr, kpE, kmE)
    A, P, da, dp = d["A"], d["P"], d["da"], d["dp"]
    nodes, w = tree(T, a0, p0, moves, weights)
    sgn = np.sign(d["SAE"])
    V = {h: np.zeros((len(A), len(P))) for (h, _, _) in nodes(T)}
    slope_max = 0.0; n_edges = 0; n_mono = 0; n_t1 = 0
    for t in range(T - 1, -1, -1):
        Vt = {}
        for (h, at, pt) in nodes(t):
            cont = None if t == T - 1 else sum(w[b] * V[h + (b,)] for b in range(len(w)))
            G = stay(d, at, pt, cont)
            Vt[h], aA, pPost, U = step(d, G)
            lo, hi, heldA = bands_from_post(d, aA, pPost)
            ok = ~np.isnan(lo)
            # part 2: fund edges monotone in the ETF incumbent, with the sign of Sigma_AE (one grid step of slack)
            dlo = np.diff(lo[ok]); dhi = np.diff(hi[ok])
            if sgn > 0:
                check(np.all(dlo <= da + 1e-12) and np.all(dhi <= da + 1e-12), f"{name}: fund edge rises with the ETF incumbent at t={t} node={h}")
            elif sgn < 0:
                check(np.all(dlo >= -da - 1e-12) and np.all(dhi >= -da - 1e-12), f"{name}: fund edge falls with the ETF incumbent at t={t} node={h}")
            n_mono += 1
            # ETF edges monotone in the fund holding: the ETF's optimizer at fund holding a from incumbent p
            tot = d["costE"][None, :, :] + G[:, None, :]; pE = np.argmin(tot, axis=2)    # (a, p) -> p'
            heldE = (pE == np.arange(len(P))[None, :])
            loE = np.array([P[np.where(heldE[i])[0].min()] if heldE[i].any() else np.nan for i in range(len(A))])
            hiE = np.array([P[np.where(heldE[i])[0].max()] if heldE[i].any() else np.nan for i in range(len(A))])
            okE = ~np.isnan(loE)
            if sgn > 0:
                check(np.all(np.diff(loE[okE]) <= dp + 1e-12) and np.all(np.diff(hiE[okE]) <= dp + 1e-12), f"{name}: ETF edge rises with the fund holding at t={t} node={h}")
            elif sgn < 0:
                check(np.all(np.diff(loE[okE]) >= -dp - 1e-12) and np.all(np.diff(hiE[okE]) >= -dp - 1e-12), f"{name}: ETF edge falls with the fund holding at t={t} node={h}")
            # slope observation (Not shown): |d lo / d p| against rho_A, on interior edges
            inner = ok & (lo > A[0] + 1e-12) & (hi < A[-1] - 1e-12)
            if inner.sum() > 2:
                s = np.abs(np.diff(lo[inner])) / dp; slope_max = max(slope_max, float(s.max()))
            # part 1: the exact last-review edge functions of the ETF incumbent
            if t == T - 1:
                for (edge, kA, sgnA) in ((lo, d["kpA"], -1.0), (hi, d["kmA"], +1.0)):
                    idle = at - d["rhoA"] * (P - pt) + sgnA * kA / (d["gamma"] * d["sA2"])
                    if sgnA < 0:
                        bought = at - (d["kpA"] - d["rho"] * d["kpE"]) / d["cres"]; sold = at - (d["kpA"] + d["rho"] * d["kmE"]) / d["cres"]
                    else:
                        bought = at + (d["kmA"] + d["rho"] * d["kpE"]) / d["cres"]; sold = at + (d["kmA"] - d["rho"] * d["kmE"]) / d["cres"]
                    pred = median3(np.full_like(P, bought), idle, np.full_like(P, sold))
                    use = ok & (pred > A[0] + 2 * da) & (pred < A[-1] - 2 * da)
                    # ETF box slack at the edge: its optimizer interior
                    ipe = np.array([pPost[np.searchsorted(A, e), j] if not np.isnan(e) else 0 for j, e in enumerate(edge)])
                    use &= (ipe > 0) & (ipe < len(P) - 1)
                    if use.any():
                        err = np.max(np.abs(edge[use] - pred[use]))
                        check(err <= 1.5 * da + 1e-12, f"{name}: last-review edge differs from the median formula by {err:.4f} at node={h}")
                        n_t1 += int(use.sum())
                # the bend's length in the ETF incumbent equals the ETF's residual static width
                bend = d["rho"] * (d["kpE"] + d["kmE"]) / d["cres"] / d["rhoA"] if d["rhoA"] != 0 else np.nan
                if not np.isnan(bend):
                    check(abs(bend - (d["kpE"] + d["kmE"]) / d["cresE"]) < 1e-12, f"{name}: bend length differs from the ETF's residual width")
            n_edges += int(ok.sum())
        V = Vt
    print(f"{name}: ok  (corr {corr}, rho_A {d['rhoA']:.3f}; {n_mono} monotonicity checks, {n_t1} last-review edge points, {n_edges} bands; max |d lo/d p| on interior edges {slope_max:.3f} against rho_A {d['rhoA']:.3f})")
    return d


# part 1 and 2, positive and negative correlation, costly ETF
run("costly ETF 20 bp, corr 0.8", 0.8, 0.002, 0.002)
run("costly ETF 20 bp, corr 0.3", 0.3, 0.002, 0.002)
run("costly ETF 20 bp, corr -0.5", -0.5, 0.002, 0.002, p0=1.2)
run("costly ETF, asymmetric rates, corr 0.6", 0.6, 0.003, 0.001)
run("frictionless ETF, corr 0.8", 0.8, 0.0, 0.0)

# part 3: frozen ETF equals the one-instrument dynamic program with the idle-ETF target
d = make(0.8, 0.002, 0.002); T = 3
A, P = d["A"], d["P"]
nodes, w = tree(T, 0.45, 1.0, ((+0.05, +0.06), (-0.05, -0.06)))
V = {h: np.zeros((len(A), len(P))) for (h, _, _) in nodes(T)}
V1 = {h: np.zeros((len(A), len(P))) for (h, _, _) in nodes(T)}
n3 = 0
for t in range(T - 1, -1, -1):
    Vt, V1t = {}, {}
    for (h, at, pt) in nodes(t):
        cont = None if t == T - 1 else sum(w[b] * V[h + (b,)] for b in range(len(w)))
        G = stay(d, at, pt, cont)
        Vt[h], aA, _, _ = step(d, G, frozen=True)
        # one-instrument DP per ETF column with the idle target a* - rho_A (p - p*), curvature gamma Sigma_AA
        aidle = at - d["rhoA"] * (P - pt)
        G1 = 0.5 * d["gamma"] * d["sA2"] * (A[:, None] - aidle[None, :]) ** 2
        if t < T - 1:
            G1 = G1 + sum(w[b] * V1[h + (b,)] for b in range(len(w)))
        tot = d["costA"][:, :, None] + G1[None, :, :]; a1 = np.argmin(tot, axis=1)
        V1t[h] = np.take_along_axis(tot, a1[:, None, :], axis=1)[:, 0, :]
        check(np.array_equal(aA, a1), f"part 3: frozen-ETF fund trades differ from the idle-target one-instrument DP at t={t} node={h}")
        n3 += 1
    V, V1 = Vt, V1t
print(f"part 3: ok  ({n3} nodes; frozen-ETF trades equal the one-instrument DP with target a* - rho_A (p - p*))")

if FAIL:
    print(f"{len(FAIL)} check(s) failed"); sys.exit(1)
print("all checks passed")
