"""Red's independent reproduction of experiment 023 Part A headlines, written from the Design only (not partA.py,
fastdp.py or report.py). P1: experiment 021's one-fund, one-ETF instance (red's own 021 reproduction of the
instance), unmarked, predictive S_t, 20-point Gauss-Hermite belief law on 41 points; no-trade-set (NT) sections
along each instrument through the other's frictionless grid target, width against the instrument's own static
width. P2 at t = T-1: the last review has no continuation, so its NT set is computed from the static objective;
fund-1 section centre slope on the ETF holding against the exact 2c parallelotope section."""
import sys
import numpy as np
from multiprocessing import Pool

LAMM, SDM = 0.0184, 0.0854
AM, AS, SDA, SDE, CE = -0.0019, 0.0035, 0.02, 0.002, 0.0001
GAMMA, KE = 5.0, 0.0005


def l1(v, k, h, axis):
    """max_y v(y) - k|x - y| along one axis of a grid with step h (exact on the grid)."""
    n = v.shape[axis]
    j = np.arange(n).reshape([-1 if a == axis else 1 for a in range(v.ndim)]) * k * h
    f = np.maximum.accumulate(v + j, axis=axis) - j
    b = np.flip(np.maximum.accumulate(np.flip(v - j, axis), axis=axis), axis) + j
    return np.maximum(f, b)


def sec_exact(mu, S, k, inst, it, h, n):
    """Claim 029 2c's exact last-review NT section along instrument inst, the others at their grid targets:
    -k_i <= (mu - gamma S x)_i <= k_i, one-sided at a bound (at 0 only <= k_i, at 1 only >= -k_i), x_inst in [0, 1]."""
    x = np.array(it, float) * h
    lo, hi = 0.0, 1.0
    for i in range(len(mu)):
        a = -GAMMA * S[i, inst]; b = mu[i] - GAMMA * (S[i] @ x - S[i, inst] * x[inst])
        up, dn = k[i], -k[i]
        if i != inst and it[i] == 0: dn = -np.inf
        if i != inst and it[i] == n - 1: up = np.inf
        if i == inst:   # own bounds are the x-range itself
            pass
        l_, u_ = (up - b) / a, (dn - b) / a      # a < 0
        lo, hi = max(lo, l_), min(hi, u_)
    return max(hi - lo, 0.0)


def p1(args):
    kf, T, h = args
    n = int(round(1 / h)) + 1; xs = np.linspace(0, 1, n)
    Pa = [AS ** 2]
    for t in range(T):
        Pa.append(1 / (1 / Pa[-1] + 1 / SDA ** 2))
    sd = np.sqrt(AS ** 2 - Pa[T]); mg = AM + np.linspace(-4, 4, 41) * sd
    gx, gw = np.polynomial.hermite_e.hermegauss(20); gw = gw / gw.sum()
    X1, X2 = np.meshgrid(xs, xs, indexing="ij")
    V = np.zeros((41, n, n)); out = []
    for t in reversed(range(T)):
        S = SDM ** 2 * np.ones((2, 2)) + np.diag([SDA ** 2 + Pa[t], SDE ** 2])
        q = np.sqrt(Pa[t] - Pa[t + 1]); Vn = np.zeros_like(V)
        for j, m in enumerate(mg):
            EV = np.zeros((n, n))
            if t < T - 1:
                for z, w in zip(gx, gw):
                    mp = np.clip(m + q * z, mg[0], mg[-1])
                    k = max(min(np.searchsorted(mg, mp) - 1, 39), 0); a = (mp - mg[k]) / (mg[k + 1] - mg[k])
                    EV += w * ((1 - a) * V[k] + a * V[k + 1])
            mu = np.array([LAMM + m, LAMM - CE])
            one = mu[0] * X1 + mu[1] * X2 - GAMMA / 2 * (S[0, 0] * X1 ** 2 + 2 * S[0, 1] * X1 * X2 + S[1, 1] * X2 ** 2)
            W = one + EV
            Vj = l1(l1(W, KE, h, 1), kf, h, 0)
            Vn[j] = Vj
            NT = (Vj - W) <= 1e-13
            it = np.unravel_index(np.argmax(one), one.shape)
            for inst, own, kap, sec in ((0, it[0], kf, NT[:, it[1]]), (1, it[1], KE, NT[it[0], :])):
                if not (0 < own < n - 1):
                    continue
                idx = np.flatnonzero(sec)
                if len(idx) == 0:
                    width = 0.0; lo = hi = None
                else:
                    width = (idx.max() - idx.min()) * h; lo, hi = idx.min(), idx.max()
                static = 2 * kap / (GAMMA * S[inst, inst])
                sec2c = sec_exact(mu, S, np.array([kf, KE]), inst, it, h, n)
                interior = lo is not None and lo > 0 and hi < n - 1
                out.append((t, j, inst, width, static, sec2c, interior, width >= 3 * h))
        V = Vn
    return kf, T, h, out


def p2_last(args):
    """P2 at the last review: funds 1-2 and one ETF, all Mkt loading 1; fund 2's alpha known (AM)."""
    kf, T, h = args
    n = int(round(1 / h)) + 1; xs = np.linspace(0, 1, n)
    Pa = [AS ** 2]
    for t in range(T):
        Pa.append(1 / (1 / Pa[-1] + 1 / SDA ** 2))
    t = T - 1
    S = SDM ** 2 * np.ones((3, 3)) + np.diag([SDA ** 2 + Pa[t], SDA ** 2, SDE ** 2])
    sd = np.sqrt(AS ** 2 - Pa[T]); mg = AM + np.linspace(-4, 4, 41) * sd
    X = np.meshgrid(xs, xs, xs, indexing="ij")
    k = np.array([kf, kf, KE])
    slopes, exact = [], []
    for m in mg:
        mu = np.array([LAMM + m, LAMM + AM, LAMM - CE])
        W = sum(mu[i] * X[i] for i in range(3)) - GAMMA / 2 * sum(S[i, j] * X[i] * X[j] for i in range(3) for j in range(3))
        Vv = l1(l1(l1(W, k[2], h, 2), k[1], h, 1), k[0], h, 0)
        NT = (Vv - W) <= 1e-13
        # frictionless target on the box: maximize the concave quadratic by projected coordinate ascent (fine), then round
        x = np.clip(np.linalg.solve(GAMMA * S, mu), 0, 1)
        for _ in range(2000):
            for i in range(3):
                x[i] = np.clip((mu[i] - GAMMA * (S[i] @ x - S[i, i] * x[i])) / (GAMMA * S[i, i]), 0, 1)
        if not (0 < x[0] < 1):
            continue
        i2 = int(round(x[1] / h))
        cen, eh = [], []
        for ie in range(n):
            idx = np.flatnonzero(NT[:, i2, ie])
            if len(idx) and idx.min() > 0 and idx.max() < n - 1:
                cen.append((idx.min() + idx.max()) / 2 * h); eh.append(ie * h)
        if len(cen) < 3:
            continue
        slopes.append(np.polyfit(eh, cen, 1)[0])
        # exact 2c section: |g_i| <= k_i where g = gamma S (x - x*) evaluated with the frictionless first-order
        # conditions; fund 2 held at its target (a bound when x2* = 0: one-sided condition g_2 >= -k_2).
        def sec(e):
            lo, hi = -np.inf, np.inf
            # gradient of the one-period score at (x1, x2, e): mu - gamma S x ; NT iff for each i: -k_i <= grad_i <= k_i,
            # one-sided at a bound (at 0 only grad_i <= k_i; at 1 only grad_i >= -k_i)
            x2 = i2 * h
            for i in range(3):
                a = -GAMMA * S[i, 0]; b = mu[i] - GAMMA * (S[i, 1] * x2 + S[i, 2] * e)
                # grad_i = a x1 + b, a < 0
                up = k[i]; dn = -k[i]
                if i == 1 and x2 <= 0: dn = -np.inf
                if i == 1 and x2 >= 1: up = np.inf
                if i == 2 and e <= 0: dn = -np.inf
                if i == 2 and e >= 1: up = np.inf
                l_, u_ = (up - b) / a, (dn - b) / a
                lo, hi = max(lo, l_), min(hi, u_)
            return lo, hi
        ce = [(sum(sec(e)) / 2, e) for e in eh if np.isfinite(sum(sec(e)))]
        exact.append(np.polyfit([c[1] for c in ce], [c[0] for c in ce], 1)[0])
    return kf, T, h, (np.median(slopes) if slopes else np.nan, len(slopes), np.median(exact) if exact else np.nan,
                      -SDM ** 2 / (SDM ** 2 + SDA ** 2 + Pa[T - 1]))


if __name__ == "__main__":
    part = sys.argv[1] if len(sys.argv) > 1 else "A"
    if part == "P1":
        hh = 1 / float(sys.argv[2]) if len(sys.argv) > 2 else 1 / 400
        kfs = [float(x) * 1e-4 for x in sys.argv[3].split(',')] if len(sys.argv) > 3 else (1e-4, 5e-4, 20e-4, 100e-4)
        jobs = [(kf, T, hh) for kf in kfs for T in (4, 8, 20)]
        with Pool(6) as pool:
            res = pool.map(p1, jobs)
        viol = 0; h = jobs[0][2]
        etf = {4: [], 8: [], 20: []}
        for kf, T, h, out in res:
            f = [o for o in out if o[2] == 0]; e = [o for o in out if o[2] == 1]
            for o in out:
                if o[3] > o[4] + 2 * h + 1e-12:
                    viol += 1
            last = [abs(o[3] - o[5]) / h for o in out if o[0] == T - 1 and o[6]]
            fine_f = [o[3] / o[4] for o in f if o[0] < T - 1 and (kf > 1e-4)]
            fine_e = [o[3] / o[4] for o in e if o[0] < T - 1 and (kf > 1e-4 or True)]
            unres_e = sum(1 for o in e if o[0] < T - 1 and not o[7])
            etf[T] += fine_e
            print(f"P1 kf {kf*1e4:.0f}bp T {T}: fund bands {len(f)} ETF bands {len(e)}; max width/static fund {max(o[3]/o[4] for o in f):.3f} "
                  f"ETF {max(o[3]/o[4] for o in e):.3f}; T-1 |NT - 2c| max {max(last):.2f}h; fund t<T-1 {len(fine_f)} median "
                  f"{np.median(fine_f) if fine_f else float('nan'):.3f}; ETF t<T-1 {len(fine_e)} median {np.median(fine_e):.3f} (below 3h: {unres_e})", flush=True)
        print("violations beyond 2h:", viol)
        for T in (4, 8, 20):
            print(f"ETF pooled over fund rates, T {T}: cells {len(etf[T])} median width/static {np.median(etf[T]):.3f}")
    else:
        jobs = [(kf, T, 1 / 40) for kf in (1e-4, 5e-4, 20e-4, 100e-4) for T in (4, 8, 20)]
        with Pool(6) as pool:
            res = pool.map(p2_last, jobs)
        for kf, T, h, (sl, nb, ex, ff) in res:
            print(f"P2 T-1 kf {kf*1e4:.0f}bp T {T} h 1/40: belief points {nb} median slope {sl:.3f}; exact 2c slope {ex:.3f}; -S_1E/S_11 {ff:.3f}", flush=True)
