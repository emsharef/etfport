"""Red's reproduction of experiment 031 (claims 036 and 038 B3), written without reading run.py or checks/036.

Reference: the full LQ over 3 funds + 2 ETFs, with a joint Kalman filter on (alpha (3), premia (2)).
- Returns r = H theta + B eps_f + resid, with H = [E | B] (E selects funds), obs noise R = B F B' + diag(sigma_A^2 funds, 0 ETFs).
- Holdings x (5) chosen at each review to maximize x'H m - gamma/2 x'Sigma_t x - 1/2 (x - x_)'Lam(x - x_) + rho V_{t+1}.
  Sigma_t = H P_t H' + R; E_t m_{t+1} = Phi m_t + (I - Phi) theta_bar.
- V_t(x_, m) = -1/2 x_'A x_ + x_'(C m + c) + (terms free of x_), solved backward exactly.
Formula side: the scalar recursion of claim 036 (d, a, weights w, ell, Dur, w~), coded here from the claim's text.
"""
import numpy as np
from scipy.optimize import brentq

SA2 = 0.02 ** 2; GAM = 5.0
BF = np.array([[1, 0.5], [1, 0.2], [1, -0.3]]); BE = np.array([[1, 0], [0.9, 0.4]])
B = np.vstack([BF, BE])                                   # 5 x 2 factor loadings
F = np.array([[0.07 ** 2, 0.3 * 0.07 * 0.04], [0.3 * 0.07 * 0.04, 0.04 ** 2]])   # factor cov (red's choice)
E = np.vstack([np.eye(3), np.zeros((2, 3))])
H = np.hstack([E, B])                                     # 5 x 5: returns' mean in theta = (alpha, premia)
R = B @ F @ B.T + np.diag([SA2] * 3 + [0, 0])


def filter_path(P0, T, Phi, Q, freeze_prem=False):
    P = [P0]
    for _ in range(T):
        Pc = P[-1]; S = H @ Pc @ H.T + R
        Pp = Pc - Pc @ H.T @ np.linalg.solve(S, H @ Pc)
        Pn = Phi @ Pp @ Phi.T + Q
        if freeze_prem: Pn[3:, 3:] = P0[3:, 3:]; Pn[3:, :3] = 0; Pn[:3, 3:] = 0
        P.append(Pn)
    return P


def solve(Ps, T, lamA, lamE, rho, Phi, tbar, t0=0):
    """Backward LQ over reviews t0..T-1; returns per-t (D^{-1}Lam, D^{-1}K, D^{-1}k0) with x* = D^-1(Lam x_ + K m + k0)."""
    Lam = np.diag([lamA] * 3 + [lamE] * 2)
    A = np.zeros((5, 5)); C = np.zeros((5, 5)); c = np.zeros(5); out = {}
    for t in range(T - 1, t0 - 1, -1):
        Sig = H @ Ps[t] @ H.T + R
        D = GAM * Sig + Lam + rho * A
        K = H + rho * C @ Phi; k0 = rho * (C @ ((np.eye(5) - Phi) @ tbar) + c)
        Di = np.linalg.inv(D)
        out[t] = (Di @ Lam, Di @ K, Di @ k0)
        A = Lam - Lam @ Di @ Lam; C = Lam @ Di @ K; c = Lam @ Di @ k0
    return out


def fund1(sol_t):
    DL, DK, _ = sol_t
    g = 1 - DL[0, 0]; h = DK[0, 0]            # u_1 = -g x_1 + h alpha_hat_1 + ... (other terms vanish as lamE -> 0)
    return g, h / g                          # rate, aim coefficient on alpha_hat_1


def P0_of(kap0, sprem=0.0):
    s2 = kap0 * SA2 / (1 - kap0)
    return np.diag([s2] * 3 + [sprem ** 2] * 2), s2


# ---------- formula side (claim 036 / 038 B3), scalar ----------
def p_scalar(s2, T, phi=1.0, Q=0.0):
    p = [s2]
    for _ in range(T):
        pp = p[-1] - p[-1] ** 2 / (p[-1] + SA2); p.append(phi ** 2 * pp + Q)
    return p


def rec(lam, rho, p, T):
    a = [0.0] * (T + 1); d = [0.0] * T
    for t in range(T - 1, -1, -1):
        d[t] = lam + GAM * (SA2 + p[t]) + rho * a[t + 1]; a[t] = lam - lam ** 2 / d[t]
    return a, d


def wts(lam, rho, p, T, t):
    a, d = rec(lam, rho, p, T); w = []; pr = 1.0
    for s in range(t, T):
        w.append(pr * GAM * (SA2 + p[s]) / (d[s] - lam)); pr *= rho * a[s + 1] / (d[s] - lam)
    return np.array(w), a


def g_const(lam, r, rho, n):
    a = 0.0
    for _ in range(n): a = lam - lam ** 2 / (lam + r + rho * a)
    return a / lam


def formulas(lam, rho, p, T, t, phi=1.0):
    w, a = wts(lam, rho, p, T, t); ps = np.array(p[t:T])
    ell = float(np.sum(w * SA2 / (SA2 + ps))); L = ell * (SA2 + p[t]) / SA2
    kap = p[t] / (SA2 + p[t]); dur = float(np.sum(w * np.arange(len(w))))
    wt = w * SA2 / (SA2 + ps); wt = wt / wt.sum(); M = float(np.sum(wt * phi ** np.arange(len(w))))
    return dict(L=L, kap=kap, dur=dur, g=a[t] / lam, wtt=wt[0], M=M, wsum=w.sum())


KAPS = [0.01, 0.03, 0.1, 0.23, 0.5, 0.75]; CR = [0.01, 0.1, 1, 10, 100]; TS = [2, 4, 8, 20]; RHOS = [0.95, 1.0]
LAMES = [1e-6, 1e-8, 1e-10]
I5 = np.eye(5); Z5 = np.zeros(5)


def part1_2():
    print("== Parts 1-2 and B3 ==")
    for lamE in LAMES:
        errL = errg = 0; nlow = nfo = nb3 = 0; npairs = 0; min_exc = np.inf; s_fo = s_b3 = 0
        p2_bad = 0; p2_id = 0; ratios = []; Lone_bad = 0
        for kap0 in KAPS:
            P0, s2 = P0_of(kap0)
            for cr in CR:
                lam = cr * GAM * SA2
                for T in TS:
                    Ps = filter_path(P0, T, I5, np.zeros((5, 5))); p = [P[0, 0] for P in Ps]
                    for rho in RHOS:
                        sol = solve(Ps, T, lam, lamE, rho, I5, Z5)
                        for t in range(T):
                            g, aim = fund1(sol[t])
                            Pst = [Ps[t]] * (T + 1); solS = solve(Pst, T, lam, lamE, rho, I5, Z5, t0=t)
                            gS, aimS = fund1(solS[t]); L = aim / aimS
                            f = formulas(lam, rho, p, T, t); npairs += 1
                            errL = max(errL, abs(L - f["L"])); errg = max(errg, abs(g - f["g"]))
                            k = f["kap"]; tol = 1e-12
                            nlow += L < 1 - tol; nfo += L > 1 / (1 - k) + tol
                            b3 = (k / (1 - k)) ** 2 * f["dur"]; nb3 += L - 1 > b3 + tol
                            if t < T - 1:
                                min_exc = min(min_exc, L - 1); s_fo = max(s_fo, (L - 1) / (k / (1 - k))); s_b3 = max(s_b3, (L - 1) / b3)
                            else:
                                Lone_bad += abs(L - 1) > 1e-6
                            # part 2 (formula quantities; reference realized trade)
                            gc = g_const(lam, GAM * (SA2 + p[t]), rho, T - t); gl = g_const(lam, GAM * SA2, rho, T - t)
                            p2_bad += not (g <= gS + 1e-9 and gS - g <= gc - gl + 1e-9)
                            for xm in [0.0, 0.5, 2.0]:
                                x_ = xm * aimS; u = g * (aim - x_); uS = gS * (aimS - x_)
                                p2_id = max(p2_id, abs(u - uS - ((g - gS) * (aimS - x_) + g * (L - 1) * aimS)))
                                bnd = (gc - gl) * abs(aimS - x_) + g * k / (1 - k) * abs(aimS)
                                p2_bad += abs(u - uS) > bnd + 1e-9 * abs(aimS)
                                if bnd > 0: ratios.append(abs(u - uS) / bnd)
        print(f" lamE {lamE:g}: pairs {npairs}, max|L_ref - L_formula| {errL:.2g}, max|g_ref - g| {errg:.2g}; "
              f"L<1 {nlow}, L>1/(1-k) {nfo}, B3 misses {nb3}; L=1 at T-1 failures {Lone_bad}; "
              f"min L-1 (t<T-1) {min_exc:.2g}; max slack ratios first-order {s_fo:.3f}, B3 {s_b3:.3f}; "
              f"part 2 failures {p2_bad}, identity resid {p2_id:.1g}, bound ratio max {max(ratios):.3f} median {np.median(ratios):.4f}")


def named():
    print("== Named points (T = 12, rho = 1, t = 0) ==")
    for name, s2r, lr in [("equity", 0.03, 0.1), ("fixed-income", 0.3, 0.5)]:
        s2 = s2r * SA2; kap0 = s2 / (SA2 + s2); P0, _ = P0_of(kap0); T = 12
        Ps = filter_path(P0, T, I5, np.zeros((5, 5))); p = [P[0, 0] for P in Ps]
        _, aim = fund1(solve(Ps, T, lr, 1e-10, 1.0, I5, Z5)[0]); _, aimS = fund1(solve([Ps[0]] * 13, T, lr, 1e-10, 1.0, I5, Z5)[0])
        f = formulas(lr, 1.0, p, T, 0); k = f["kap"]
        print(f" {name}: kappa {k:.4f}, Dur_0 {f['dur']:.3f}, L ref {aim / aimS:.4f} formula {f['L']:.4f}, "
              f"B3 {1 + (k / (1 - k)) ** 2 * f['dur']:.4f}, first-order {1 / (1 - k):.4f}")


def M_ref(kap0, lam, rho, T, t, phi, stat, lamE=1e-10):
    P0, s2 = P0_of(kap0); Q = np.diag([(1 - phi ** 2) * s2 if stat else 0.0] * 3 + [0, 0])
    Phi = np.diag([phi] * 3 + [1, 1]); Ps = filter_path(P0, T, Phi, Q)
    _, a_phi = fund1(solve(Ps, T, lam, lamE, rho, Phi, Z5)[t]); _, a_one = fund1(solve(Ps, T, lam, lamE, rho, I5, Z5)[t])
    return a_phi / a_one, [P[0, 0] for P in Ps]


def part3():
    print("== Part 3 ==")
    for lamE in LAMES:
        err = 0; nbr = 0; n = 0; m1 = 0
        for kap0 in KAPS:
            for cr in CR:
                lam = cr * GAM * SA2
                for T in TS:
                    for rho in RHOS:
                        for phi in [0, 0.5, 0.8, 0.95, 1]:
                            for stat in [True, False]:
                                P0, s2 = P0_of(kap0); Q = np.diag([(1 - phi ** 2) * s2 if stat else 0.0] * 3 + [0, 0])
                                Phi = np.diag([phi] * 3 + [1, 1]); Ps = filter_path(P0, T, Phi, Q); p = [P[0, 0] for P in Ps]
                                sp = solve(Ps, T, lam, lamE, rho, Phi, Z5); s1 = solve(Ps, T, lam, lamE, rho, I5, Z5)
                                for t in range(T):
                                    M = fund1(sp[t])[1] / fund1(s1[t])[1]; f = formulas(lam, rho, p, T, t, phi); n += 1
                                    err = max(err, abs(M - f["M"])); lo = f["wtt"] + (1 - f["wtt"]) * phi ** (T - 1 - t)
                                    nbr += not (lo - 1e-7 <= M <= 1 + 1e-7)
                                    if phi == 1: m1 = max(m1, abs(M - 1))
        print(f" lamE {lamE:g}: pairs {n}, max|M_ref - M_formula| {err:.2g}, bracket misses (margin 1e-7) {nbr}, max|M(1)-1| {m1:.1g}")
    for name, s2r, lr in [("equity", 0.03, 0.1), ("fixed-income", 0.3, 0.5)]:
        k0 = s2r / (1 + s2r); Ms = [M_ref(k0, lr, 1.0, 12, 0, ph, True)[0] for ph in np.linspace(0, 1, 101)]
        print(f" {name}: M_0 nondecreasing in phi on 101 points: {all(np.diff(Ms) >= -1e-9)}; M_0(0) {Ms[0]:.3f}, M_0(1) {Ms[-1]:.6f}")


def part4_and_notshown():
    print("== Part 4 ==")
    for cr in [1e-4, 1e-3, 1e-2]:
        mL = mM = 0
        for kap0 in KAPS:
            for T in TS:
                for rho in RHOS:
                    lam = cr * GAM * SA2; P0, _ = P0_of(kap0); Ps = filter_path(P0, T, I5, np.zeros((5, 5)))
                    _, aim = fund1(solve(Ps, T, lam, 1e-10, rho, I5, Z5)[0]); _, aimS = fund1(solve([Ps[0]] * (T + 1), T, lam, 1e-10, rho, I5, Z5)[0])
                    mL = max(mL, aim / aimS - 1); mM = max(mM, 1 - M_ref(kap0, lam, rho, T, 0, 0.5, True)[0])
        print(f" cost ratio {cr:g}: max L_0 - 1 {mL:.2g}, max 1 - M_0(0.5) {mM:.2g}")
    # ETF trade independence of premium futures, at the same current belief
    T = 8; m = np.array([0.002, 0.001, -0.001, 0.015, 0.005]); x_ = np.array([0.3, 0.1, 0.0, -0.2, 0.1])
    for lamE in LAMES:
        dpers = dlearn = 0; big = 0
        for kap0 in KAPS:
            for cr in CR:
                for rho in RHOS:
                    lam = cr * GAM * SA2; P0, _ = P0_of(kap0, 0.005)
                    trades = {}
                    for key, psi, Qp, frz in [("psi1", 1.0, 0.0, False), ("psi.5", 0.5, 0.75 * 0.005 ** 2, False), ("frozen", 1.0, 0.0, True)]:
                        Phi = np.diag([1, 1, 1, psi, psi]); Q = np.diag([0, 0, 0, Qp, Qp]); tb = np.array([0, 0, 0, 0.004, 0.002])
                        Ps = filter_path(P0, T, Phi, Q, frz); DL, DK, dk = solve(Ps, T, lam, lamE, rho, Phi, tb)[0]
                        trades[key] = (DL @ x_ + DK @ m + dk - x_)[3:]
                    dpers = max(dpers, np.abs(trades["psi1"] - trades["psi.5"]).max()); dlearn = max(dlearn, np.abs(trades["psi1"] - trades["frozen"]).max())
                    big = max(big, np.abs(trades["psi1"]).max())
        print(f" lamE {lamE:g}: ETF trade diff, premium persistence 0.5 vs 1: {dpers:.2g}; frozen vs learning premium precision: {dlearn:.2g}; largest ETF trade {big:.2g}")
    print("== Not shown (counted) ==")
    fl = fT = nl = nT = 0
    for kap0 in KAPS:
        P0, _ = P0_of(kap0)
        for rho in RHOS:
            for T in TS:
                p = [P[0, 0] for P in filter_path(P0, T, I5, np.zeros((5, 5)))]
                for t in range(T - 1):
                    Ls = [formulas(cr * GAM * SA2, rho, p, T, t)["L"] for cr in CR]
                    fl += sum(Ls[i + 1] < Ls[i] - 1e-12 for i in range(4)); nl += 4
            for cr in CR:
                LT = [formulas(cr * GAM * SA2, rho, [P[0, 0] for P in filter_path(P0, T, I5, np.zeros((5, 5)))], T, 0)["L"] for T in TS]
                fT += sum(LT[i + 1] < LT[i] - 1e-12 for i in range(3)); nT += 3
    print(f" L-1 falls as lambda_A rises: {fl}/{nl}; L_0-1 falls as T rises: {fT}/{nT}")


def levelsets():
    print("== Level sets (T = 20, t = 0, rho = 1; 13 cost ratios) ==")
    crs = np.logspace(-2, 2, 13); T = 20
    for th in [0.01, 0.05, 0.1]:
        ex = []
        for cr in crs:
            lam = cr * GAM * SA2
            def fL(k):
                P0, _ = P0_of(k); Ps = filter_path(P0, T, I5, np.zeros((5, 5)))
                _, a = fund1(solve(Ps, T, lam, 1e-10, 1.0, I5, Z5)[0]); _, aS = fund1(solve([Ps[0]] * (T + 1), T, lam, 1e-10, 1.0, I5, Z5)[0])
                return a / aS - 1 - th
            ex.append(brentq(fL, 1e-4, 0.95, xtol=1e-6) if fL(0.95) > 0 else np.nan)
        print(f" learning theta {th}: exact kappa crossings {np.round(ex, 3).tolist()} ; first-order {th / (1 + th):.3f}")
    kap0 = 0.23
    for th in [0.01, 0.05, 0.1]:
        ex = []; bd = []
        for cr in crs:
            lam = cr * GAM * SA2
            fM = lambda ph: 1 - M_ref(kap0, lam, 1.0, T, 0, ph, True)[0] - th
            def fB(ph):
                _, p = M_ref(kap0, lam, 1.0, T, 0, ph, True); f = formulas(lam, 1.0, p, T, 0, ph)
                return (1 - f["wtt"]) * (1 - ph ** (T - 1)) - th
            ex.append(brentq(fM, 0, 0.99999, xtol=1e-6) if fM(0) > 0 else np.nan)
            bd.append(brentq(fB, 0, 0.99999, xtol=1e-6) if fB(0) > 0 else np.nan)
        print(f" mean reversion theta {th}: exact phi {np.round(ex, 3).tolist()}\n   bound phi {np.round(bd, 3).tolist()}")


if __name__ == "__main__":
    named(); part1_2(); part3(); part4_and_notshown(); levelsets()
