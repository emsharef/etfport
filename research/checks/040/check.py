"""Solver checks of claim 040 (M7, one review, ETFs at their zero bound); not its proof.

Run: uv run python checks/040/check.py

 (i)   part 2: the exposure problem in ETF coordinates: the active-set closed form for w(q), zeta(q) and Z(q) against
       cvxpy's joint optimum; the gradient of V_E is -zeta (central differences);
 (ii)  part 3: at the joint optimum every fund's marginal alpha^Z_i - gamma (V^Z x^A)_i sits on its band edge or inside
       its band with the right sign; the hold test (incumbent optimal iff every fund in band) both ways; alpha^Z, V^Z
       equal claim 031's reduced moments for the menu with Z removed;
 (iii) part 4: one fund's marginal m(x) along its holding is continuous, nonincreasing, piecewise linear with slope
       -gamma s^Z on each piece; the optimum is the root; the drop-Z rule is exact iff its target stays in the
       incumbent's piece, and errs in the stated direction otherwise;
 (iv)  part 5(a): one ETF is at zero iff mu_E <= gamma sigma_EE q.
Random assumed inputs (rule 22: illustrations, nothing decided by them). Floating point, not a certificate.
"""
import itertools
import sys

import cvxpy as cp
import numpy as np

rng = np.random.default_rng(40)
TOL = 5e-4   # CLARABEL lands within a few 1e-4 of a kink
FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg); print("FAIL:", msg)


# ---------- instances and the joint solve ----------
def instance(N=3, M=2, fees=True, lam_scale=1.0, x_inc=None):
    K = M
    BA = rng.uniform(-0.5, 1.5, (N, K))
    BE = rng.uniform(0.5, 1.5, (M, K)) * (0.7 * np.eye(M) + 0.3)
    Sf = np.diag(rng.uniform(0.002, 0.01, K)); Pl = np.diag(rng.uniform(0.0, 0.001, K))
    v = rng.uniform(0.0005, 0.004, N)
    cE = rng.uniform(-0.0005, 0.001, M) if fees else np.zeros(M)
    lam = lam_scale * rng.uniform(-0.02, 0.02, K)
    alpha = rng.uniform(-0.01, 0.015, N)
    kpA = rng.uniform(0.0, 0.01, N); kmA = rng.uniform(0.0, 0.01, N)
    gamma = rng.uniform(2.0, 6.0)
    B = np.vstack([BA, BE]); St = Sf + Pl
    Sig = B @ St @ B.T + np.diag(np.concatenate([v, np.zeros(M)]))
    mu = np.concatenate([alpha + BA @ lam, BE @ lam - cE])
    xmA = rng.uniform(0.0, 0.5, N) if x_inc is None else x_inc
    xm = np.concatenate([xmA, rng.uniform(0.0, 0.3, M)])
    R = np.linalg.inv(BE); Q = R.T @ BA.T
    return dict(N=N, M=M, K=K, BA=BA, BE=BE, St=St, v=v, cE=cE, lam=lam, alpha=alpha, kp=kpA, km=kmA, gamma=gamma,
                Sig=Sig, mu=mu, xm=xm, xbarA=np.full(N, 5.0), R=R, Q=Q,
                muE=BE @ lam - cE, SEE=BE @ St @ BE.T, at=alpha + Q.T @ cE)


def solve_joint(d, xmA=None):
    N, M = d["N"], d["M"]
    xm = d["xm"].copy()
    if xmA is not None: xm[:N] = xmA
    x = cp.Variable(N + M); u = x[:N] - xm[:N]
    cost = cp.sum(cp.multiply(d["kp"], cp.pos(u)) + cp.multiply(d["km"], cp.pos(-u)))
    obj = d["mu"] @ x - 0.5 * d["gamma"] * cp.quad_form(x, cp.psd_wrap(d["Sig"])) - cost
    prob = cp.Problem(cp.Maximize(obj), [x >= 0, x[:N] <= d["xbarA"]])   # no ETF caps, no budget
    prob.solve(solver=cp.CLARABEL)
    return np.array(x.value).ravel(), prob.value


# ---------- part 2: the exposure problem by active sets ----------
def expo(d, q):
    """w(q), zeta(q), Z(q) for max mu_E'w - (gamma/2) w'S w over w >= q, by enumeration of active sets (M small)."""
    M, g, muE, S = d["M"], d["gamma"], d["muE"], d["SEE"]
    best = None
    for r in range(M + 1):
        for Z in itertools.combinations(range(M), r):
            Z = list(Z); c = [j for j in range(M) if j not in Z]
            w = np.zeros(M); zeta = np.zeros(M)
            w[Z] = q[Z]
            if c:
                w[c] = np.linalg.solve(S[np.ix_(c, c)], muE[c] / g - S[np.ix_(c, Z)] @ q[Z])
            zeta[Z] = g * (S[np.ix_(Z, Z)] @ q[Z] + S[np.ix_(Z, c)] @ w[c]) - muE[Z] if Z else np.zeros(0)
            if np.all(zeta[Z] >= -1e-12) and np.all(w[c] >= q[c] - 1e-12):
                if best is None: best = (w, zeta, Z)
                else: check(np.allclose(w, best[0], atol=1e-9), "two active sets satisfy complementarity with different w")
    check(best is not None, "no active set satisfies complementarity")
    return best


def V_E(d, q):
    w, _, _ = expo(d, q); return d["muE"] @ w - 0.5 * d["gamma"] * w @ d["SEE"] @ w


def reduced_moments(d, Z):
    """alpha^Z, V^Z of part 3 for a given at-zero set Z."""
    M, g = d["M"], d["gamma"]; c = [j for j in range(M) if j not in Z]
    S, muE, Q = d["SEE"], d["muE"], d["Q"]
    if not Z: return d["at"].copy(), np.diag(d["v"]).copy()
    if c:
        Scc_inv = np.linalg.inv(S[np.ix_(c, c)])
        schur = S[np.ix_(Z, Z)] - S[np.ix_(Z, c)] @ Scc_inv @ S[np.ix_(c, Z)]
        mu_h = muE[Z] - S[np.ix_(Z, c)] @ Scc_inv @ muE[c]
    else:
        schur = S.copy(); mu_h = muE.copy()
    QZ = Q[Z, :]
    return d["at"] + QZ.T @ mu_h, np.diag(d["v"]) + QZ.T @ schur @ QZ


def claim031_reduced(d, Z):
    """Claim 031's reduced fund moments for the menu with the ETFs in Z removed (c^E = 0 there)."""
    M, K = d["M"], d["K"]; c = [j for j in range(M) if j not in Z]
    BEc = d["BE"][c, :]
    if c:
        Qb, _ = np.linalg.qr(BEc.T); PiR = Qb @ Qb.T
    else:
        PiR = np.zeros((K, K))
    PiU = np.eye(K) - PiR; St = d["St"]
    SRR, SRU, SUU = PiR @ St @ PiR, PiR @ St @ PiU, PiU @ St @ PiU
    SRR_inv = np.linalg.pinv(SRR); schur = SUU - SRU.T @ SRR_inv @ SRU
    J = PiU - PiR @ SRR_inv @ SRU
    return d["alpha"] + d["BA"] @ J.T @ d["lam"], np.diag(d["v"]) + d["BA"] @ schur @ d["BA"].T


def band_ok(d, G, xA, xmA, at_opt=True, tol=TOL):
    """part 3's band conditions at xA with incumbent xmA; at_opt: bought => G = kp (or >= at cap), sold => G = -km (or <= at 0)."""
    ok = True
    for i in range(d["N"]):
        kp, km = d["kp"][i], d["km"][i]
        eps = 1e-4   # solver resolution for "traded" and "at a bound"
        if xA[i] > xmA[i] + eps:
            ok &= (abs(G[i] - kp) < tol) if xA[i] < d["xbarA"][i] - eps else (G[i] >= kp - tol)
        elif xA[i] < xmA[i] - eps:
            ok &= (abs(G[i] + km) < tol) if xA[i] > eps else (G[i] <= -km + tol)
        else:
            lo = -km if xA[i] > eps else -np.inf; hi = kp if xA[i] < d["xbarA"][i] - eps else np.inf
            ok &= (lo - tol <= G[i] <= hi + tol)
    return ok


def parts_i_ii():
    n_zero = 0; n_inst = 0; n_hold_ok = 0; n_trade_cases = 0
    for _ in range(60):
        d = instance(fees=bool(rng.integers(2)))
        N, M = d["N"], d["M"]
        x, val = solve_joint(d); xA, xE = x[:N], x[N:]
        q = d["Q"] @ xA
        w, zeta, Z = expo(d, q)
        Zsolver = [j for j in range(M) if xE[j] < 1e-6]
        check(np.allclose(w, xE + q, atol=5e-5), "part 2: active-set w(q) differs from the solver's ETF exposure")
        check(set(Z) <= set(Zsolver) or np.all(zeta[[j for j in Z if j not in Zsolver]] < 1e-6), "part 2: active set differs from the solver's zero set")
        n_zero += len(Zsolver); n_inst += 1
        # gradient of V_E is -zeta
        for j in range(M):
            h = 1e-5; e = np.zeros(M); e[j] = h
            num = (V_E(d, q + e) - V_E(d, q - e)) / (2 * h)
            check(abs(num + zeta[j]) < 1e-6 * max(1.0, abs(zeta[j]) / 1e-3), f"part 2: dV_E/dq_j {num:.3e} vs -zeta_j {-zeta[j]:.3e}")
        # part 3: fund marginals at the optimum, both forms
        G_direct = d["at"] - d["gamma"] * d["v"] * xA - d["Q"].T @ zeta
        aZ, VZ = reduced_moments(d, Z)
        G_red = aZ - d["gamma"] * VZ @ xA
        check(np.allclose(G_direct, G_red, atol=1e-10), "part 3: the two forms of the fund marginal differ")
        check(band_ok(d, G_direct, xA, d["xm"][:N]), "part 3: a fund's marginal at the optimum is off its band edge")
        # hold test: re-solve from the optimum as incumbent -> no trade; and from a random incumbent, trade iff some band fails
        x2, _ = solve_joint(d, xmA=xA)
        check(np.allclose(x2[:N], xA, atol=2e-3), "part 3: the optimum re-solved as incumbent trades a fund")
        xm_rand = rng.uniform(0.0, 0.6, N)
        w_r, zeta_r, Z_r = expo(d, d["Q"] @ xm_rand)
        G_r = d["at"] - d["gamma"] * d["v"] * xm_rand - d["Q"].T @ zeta_r
        in_band = band_ok(d, G_r, xm_rand, xm_rand, tol=1e-9)
        x3, _ = solve_joint(d, xmA=xm_rand)
        traded = np.any(np.abs(x3[:N] - xm_rand) > 1e-4)
        if in_band: check(not traded, "part 3: incumbent in every band but the solver trades")
        else:
            n_trade_cases += 1
            # a fund off its band by more than the tolerance forces a trade
            off = max(max(G_r[i] - d["kp"][i], -d["km"][i] - G_r[i]) for i in range(N))
            if off > 1e-4: check(traded, "part 3: a fund off its band but the solver holds everything")
        n_hold_ok += 1
        # claim 031's reduced moments (c^E = 0 there): compare on a copy without fees
        d0 = dict(d); d0["cE"] = np.zeros(M); d0["muE"] = d["BE"] @ d["lam"]; d0["at"] = d["alpha"].copy()
        a1, V1 = reduced_moments(d0, Z); a2, V2 = claim031_reduced(d0, Z)
        check(np.allclose(a1, a2, atol=1e-10) and np.allclose(V1, V2, atol=1e-10), "part 3: alpha^Z, V^Z differ from claim 031's reduced moments")
    print(f"  parts 2-3: {n_inst} instances, ETFs at zero in {n_zero}/{n_inst * 2} instrument slots; closed-form exposure, gradient -zeta, "
          f"band conditions at the optimum, hold test ({n_trade_cases} trading incumbents) and claim 031's moments all agree")


# ---------- part 4: one fund's path ----------
def marginal_path(d, xs):
    out = []
    for x in xs:
        q = d["Q"] @ np.array([x]); w, zeta, Z = expo(d, q)
        out.append((d["at"][0] - d["gamma"] * d["v"][0] * x - d["Q"][:, 0] @ zeta, tuple(Z)))
    return out


def part_iii():
    n_diff = 0; n_exact = 0; n_dir_ok = 0
    for _ in range(80):
        d = instance(N=1, M=3, fees=False, lam_scale=0.5)
        d["xbarA"] = np.array([3.0])
        xs = np.linspace(0.0, 3.0, 3001)
        path = marginal_path(d, xs); m = np.array([p[0] for p in path]); Zs = [p[1] for p in path]
        check(np.all(np.diff(m) <= 1e-9), "part 4: the fund's marginal increases somewhere")
        # piecewise slope -gamma s^Z inside pieces
        for k in range(1, len(xs) - 1):
            if Zs[k - 1] == Zs[k] == Zs[k + 1]:
                Z = list(Zs[k]); _, VZ = reduced_moments(d, Z)
                slope = (m[k + 1] - m[k - 1]) / (xs[k + 1] - xs[k - 1])
                check(abs(slope + d["gamma"] * VZ[0, 0]) < 1e-6, "part 4: slope differs from -gamma s^Z inside a piece")
        # the optimum is the root; compare with the solver
        xm = float(rng.uniform(0.0, 2.0)); d["xm"][0] = xm
        x, _ = solve_joint(d); xstar = x[0]
        mm = np.interp(xm, xs, m); kp, km = d["kp"][0], d["km"][0]
        if mm > kp + 1e-6:
            target = xs[np.searchsorted(-m, -kp)] if m[-1] < kp else 3.0   # largest x with m >= kp
            check(xstar > xm - 1e-4 and abs(xstar - target) < 2e-3, f"part 4: purchase target {target:.4f} vs solver {xstar:.4f}")
        elif mm < -km - 1e-6:
            target = xs[max(np.searchsorted(-m, km) - 1, 0)] if m[0] > -km else 0.0   # smallest x with m <= -km
            check(xstar < xm + 1e-4 and abs(xstar - target) < 2e-3, f"part 4: sale target {target:.4f} vs solver {xstar:.4f}")
        else:
            check(abs(xstar - xm) < 1e-4, "part 4: in band but the solver trades")
            continue
        # the drop-Z rule from the incumbent's piece
        Zm = list(expo(d, d["Q"] @ np.array([xm]))[2]); aZ, VZ = reduced_moments(d, Zm); s = VZ[0, 0]
        lo, hi = (aZ[0] - kp) / (d["gamma"] * s), (aZ[0] + km) / (d["gamma"] * s)
        xt_u = min(max(xm, lo), hi)                      # unclipped drop-Z root
        xt = min(max(xt_u, 0.0), 3.0)
        seg = [xs[k] for k in range(len(xs)) if Zs[k] == tuple(Zm)]
        first, last = min(seg), max(seg)
        in_piece = (first - 2e-3 <= xt_u <= last + 2e-3) or (xt_u < 0 and first <= 1e-9) or (xt_u > 3.0 and last >= 3.0 - 1e-9)   # end pieces extended
        same_clip = (xt_u <= 0 and xstar < 2e-3 and mm < -km) or (xt_u >= 3.0 and xstar > 3.0 - 2e-3 and mm > kp)
        if in_piece or same_clip:
            n_exact += 1; check(abs(xt - xstar) < 3e-3, f"part 4: drop-Z target {xt:.4f} should equal the solver's {xstar:.4f}")
        else:
            n_diff += 1
            check(abs(xt - xstar) > 1e-3, f"part 4: drop-Z target {xt:.4f} outside the incumbent's piece, not clipped alike, yet equals the solver's {xstar:.4f}")
            # direction: curvature along the way from xm to xt
            ks = [k for k in range(len(xs)) if min(xm, xt) - 1e-9 <= xs[k] <= max(xm, xt) + 1e-9]
            curv = [reduced_moments(d, list(Zs[k]))[1][0, 0] for k in ks]
            if all(c >= s - 1e-15 for c in curv) and max(curv) > s + 1e-12:
                n_dir_ok += 1; check(abs(xstar - xm) <= abs(xt - xm) + 3e-3, "part 4: curvature only rises yet the true trade is longer")
            elif all(c <= s + 1e-15 for c in curv) and min(curv) < s - 1e-12:
                n_dir_ok += 1; check(abs(xstar - xm) >= abs(xt - xm) - 3e-3, "part 4: curvature only falls yet the true trade is shorter")
    print(f"  part 4: marginal nonincreasing and piecewise linear with slope -gamma s^Z; targets match the solver; drop-Z rule exact in {n_exact} "
          f"trading cases, differs in {n_diff} (direction as stated in {n_dir_ok} of them with monotone curvature)")


def part_iv():
    n0 = 0
    for _ in range(100):
        d = instance(N=2, M=1, fees=bool(rng.integers(2)), lam_scale=1.5)
        x, _ = solve_joint(d); q = float((d["Q"] @ x[:2])[0]); at_zero = x[2] < 1e-6
        cond = d["muE"][0] <= d["gamma"] * d["SEE"][0, 0] * q + 1e-7
        check(at_zero == cond or abs(d["muE"][0] - d["gamma"] * d["SEE"][0, 0] * q) < 1e-6, "part 5(a): one-ETF zero condition fails")
        n0 += at_zero
    print(f"  part 5(a): one ETF at zero iff mu_E <= gamma sigma_EE q on 100 instances ({n0} at zero)")


def part_v():
    """part 3(d): d x*/d lambda_hat for one trading fund against r_Z' B^E_{Z.c} / (gamma s^Z); zero when Z is empty."""
    n_lk = 0; n_zero = 0
    for _ in range(120):
        d = instance(N=1, M=3, fees=bool(rng.integers(2)), lam_scale=float(rng.choice([0.5, 3.0])))
        d["xbarA"] = np.array([3.0]); d["xm"][0] = float(rng.uniform(0.0, 1.5))
        x, _ = solve_joint(d); x0 = x[0]
        if abs(x0 - d["xm"][0]) < 1e-3 or x0 < 1e-3 or x0 > 3.0 - 1e-3:
            continue   # held or at a bound: no first-order response
        q = d["Q"] @ np.array([x0]); w, zeta, Z = expo(d, q); c = [j for j in range(3) if j not in Z]
        if Z and np.min(zeta[Z]) < 1e-4: continue   # near-degenerate active set
        if c and np.min((w - q)[c]) < 1e-4: continue
        S, BE = d["SEE"], d["BE"]
        BZc = BE[Z, :] - S[np.ix_(Z, c)] @ np.linalg.inv(S[np.ix_(c, c)]) @ BE[c, :] if (Z and c) else (BE[Z, :] if Z else np.zeros((0, 3)))
        _, VZ = reduced_moments(d, Z); sZ = VZ[0, 0]
        pred = (d["Q"][Z, 0] @ BZc) / (d["gamma"] * sZ) if Z else np.zeros(3)
        h = 1e-3; num = np.zeros(3); crossed = False
        for k in range(3):
            e = np.zeros(3); e[k] = h
            dp = dict(d); dm = dict(d); xs_ = []
            for dd, sg in ((dp, 1.0), (dm, -1.0)):
                lam = d["lam"] + sg * e
                dd["mu"] = np.concatenate([d["alpha"] + d["BA"] @ lam, d["BE"] @ lam - d["cE"]]); dd["muE"] = d["BE"] @ lam - d["cE"]
                xp = solve_joint(dd)[0]; xs_.append(xp[0])
                if set(expo(dd, dd["Q"] @ np.array([xp[0]]))[2]) != set(Z): crossed = True   # the perturbation changes the at-zero set
                if np.sign(xp[0] - d["xm"][0]) != np.sign(x0 - d["xm"][0]) or abs(xp[0] - d["xm"][0]) < 1e-3 or xp[0] < 1e-3 or xp[0] > 3.0 - 1e-3:
                    crossed = True   # the fund stops trading, or reaches a bound, inside the stencil
            num[k] = (xs_[0] - xs_[1]) / (2 * h)
        if crossed: continue   # a breakpoint inside the difference stencil: the response is one-sided there (part 4)
        tol = 0.05 * max(1.0, np.abs(pred).max())   # solver resolution about 1e-5 in x over a 2e-3 stencil
        if not np.allclose(num, pred, atol=tol):
            print("    detail:", dict(x0=x0, xm=d["xm"][0], Z=Z, zeta=zeta, slack=w - q, num=num, pred=pred))
        check(np.allclose(num, pred, atol=tol), f"part 3(d): response {num} vs formula {pred}")
        if Z: n_lk += 1
        else: n_zero += 1
    print(f"  part 3(d): one trading fund's response to premium error matches r_Z' B^E_Z.c/(gamma s^Z) in {n_lk} cases with an ETF at zero and is zero in {n_zero} without")


def main():
    parts_i_ii(); part_iii(); part_iv(); part_v()
    if FAIL:
        print(f"checks/040: {len(FAIL)} failure(s)"); sys.exit(1)
    print("checks/040: all checks passed")


if __name__ == "__main__":
    main()
