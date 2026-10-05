"""Red's reproduction of experiment 026 (M7 single-instrument cells for claim 100), written from the registered
Design (and Deviation 1) without reading run.py, scope.py or report.py.

Cells: fund alone (loading 1, residual 2%, alpha prior N(-0.19%, 0.35%^2), premium known 1.84%) or ETF alone
(loading 1, residual 0.2%, fee 1 bp, premium prior N(1.84%, 0.54%^2)); market SD 8.54%; gamma 5.
Predictive law, two independent Gaussian factors (tensor Gauss-Hermite 20 x 20):
  fund: u = alpha - m + eps_A ~ N(0, P + sA^2) drives the belief (m' = m + P/(P + sA^2) u) and the return
        r = mu + z_f + u, z_f ~ N(0, sm^2);
  ETF:  v = f - m ~ N(0, P + sm^2) drives the belief (m' = m + P/(P + sm^2) v) and the return
        r = mu + v + eps_E, eps_E ~ N(0, sE^2).
Returns on: pre-trade holding x g with g = 1 + r; returns off: g = 1. Grid DP on x in [0, 1.5] (post-trade
x <= 1), h = 1/400, belief mean on 41 points m0 +- 4 sd(m_T - m_0), exact L1 transform for the trade.

Usage: uv run python experiments/026/red_reproduce.py [cells|scope <ff5 zip>]
"""
import sys, itertools, importlib.util, os
import numpy as np
from multiprocessing import Pool

GAM, SM, LAM_M = 5.0, 0.0854, 0.0184
X = dict(fund=dict(s=0.02, m0=-0.0019, p0=0.0035 ** 2), etf=dict(s=0.002, m0=0.0184, p0=0.0054 ** 2, fee=0.0001))
gx, gw = np.polynomial.hermite_e.hermegauss(20); gw = gw / gw.sum()


def l1(v, k, h):
    j = np.arange(v.shape[-1]) * k * h
    f = np.maximum.accumulate(v + j, axis=-1) - j
    b = np.flip(np.maximum.accumulate(np.flip(v - j, -1), axis=-1), -1) + j
    return np.maximum(f, b)


def cell(args):
    inst, T, kap, ret, h = args
    c = X[inst]; s2 = c["s"] ** 2
    P = [c["p0"]]
    obs = s2 if inst == "fund" else SM ** 2
    for t in range(T):
        P.append(1 / (1 / P[-1] + 1 / obs))
    Sig = [(SM ** 2 + s2 + P[t]) if inst == "fund" else (P[t] + SM ** 2 + s2) for t in range(T + 1)]
    mu = (lambda m: LAM_M + m) if inst == "fund" else (lambda m: m - c["fee"])
    sd = np.sqrt(c["p0"] - P[T]); mg = c["m0"] + np.linspace(-4, 4, 41) * sd
    nx = int(round(1.5 / h)) + 1; xs = np.arange(nx) * h; icap = int(round(1 / h))
    V = np.zeros((41, nx)); out = []
    for t in reversed(range(T)):
        EV = np.zeros((41, nx))
        if t < T - 1:
            K = P[t] / (P[t] + obs); sdb = np.sqrt(P[t] + obs)
            other = SM if inst == "fund" else c["s"]
            for (z1, w1), (z2, w2) in itertools.product(zip(gx, gw), zip(gx, gw)):
                b = sdb * z1                                  # belief-driving shock
                for j, m in enumerate(mg):
                    mp = np.clip(m + K * b, mg[0], mg[-1])
                    k = max(min(np.searchsorted(mg, mp) - 1, 39), 0); a = (mp - mg[k]) / (mg[k + 1] - mg[k])
                    Vm = (1 - a) * V[k] + a * V[k + 1]
                    if ret:
                        g = 1 + mu(m) + b + other * z2
                        EV[j] += w1 * w2 * np.interp(np.clip(xs * g, 0, xs[-1]), xs, Vm)
                    else:
                        EV[j] += w1 * w2 * Vm
        W = mu(mg)[:, None] * xs[None, :] - GAM / 2 * Sig[t] * xs[None, :] ** 2 + EV
        W[:, icap + 1:] = -np.inf
        Wc = W[:, :icap + 1]
        f1 = Wc - kap * xs[:icap + 1]; f2 = Wc + kap * xs[:icap + 1]
        i1 = np.array([np.flatnonzero(r >= r.max() - 1e-15)[0] for r in f1])
        i2 = np.array([np.flatnonzero(r >= r.max() - 1e-15)[-1] for r in f2])
        # value for pre-trade holdings on the whole grid: best post-trade point in [0, 1]
        Vn = np.empty((41, nx))
        for j in range(41):
            lo, hi = i1[j], i2[j]
            xp = xs
            Vn[j] = np.where(xp < xs[lo], Wc[j, lo] - kap * (xs[lo] - xp),
                             np.where(xp > xs[hi], Wc[j, hi] - kap * (xp - xs[hi]), W[j, np.minimum(np.arange(nx), nx - 1)]))
        V = Vn
        static = 2 * kap / (GAM * Sig[t])
        tgt = mu(mg) / (GAM * Sig[t])
        innov = np.sqrt(P[t] - P[t + 1]) / (GAM * Sig[t + 1]) * (1 if inst == "etf" else 1) / static
        drift = (1 / (GAM * Sig[t + 1]) - 1 / (GAM * Sig[t])) * mu(c["m0"]) / static
        for j in range(41):
            if 0 < tgt[j] < 1 and i1[j] > 0 and i2[j] < icap:
                out.append((t, j, (xs[i2[j]] - xs[i1[j]]) / static, static, innov, drift))
    return (inst, T, kap, ret, h), out, [2 * kap / (GAM * Sig[t]) for t in range(T)], 2 * kap / (GAM * (Sig[T] - P[T]))


def summarize(res, res2):
    viol = 0; dec = 0
    print("| instrument | T | kappa | returns | width/static t=0 / mid / T-2 / T-1 (median) | coarse points t<=T-2 | pure-learning t0 | innov/static t=0 | drift/static t=0 | resolved |")
    for (key, out, sw, lim), (_, out2, _, _) in zip(res, res2):
        inst, T, kap, ret, h = key
        dec += any(np.diff(sw) < -1e-15)
        viol += sum(1 for o in out if o[2] * o[3] > o[3] + 2 * h + 1e-12)
        med = lambda t: np.median([o[2] for o in out if o[0] == t]) if any(o[0] == t for o in out) else np.nan
        coarse = sum(1 for o in out if o[0] <= T - 2 and abs(o[2] * o[3] - o[3]) <= 2 * h + 1e-12)
        t0 = None
        for t0c in range(T - 1):
            if all(o[3] - o[2] * o[3] > 2 * h + 1e-12 for o in out if t0c <= o[0] <= T - 2):
                t0 = t0c; break
        d2 = {(o[0], o[1]): o[2] * o[3] for o in out2}
        both = [(o[2] * o[3], d2[(o[0], o[1])]) for o in out if (o[0], o[1]) in d2]
        resolved = sum(1 for a, b in both if abs(a - b) < 0.1 * a)
        i0 = [o for o in out if o[0] == 0]
        print(f"| {inst} | {T} | {kap*1e4:.0f} | {'on' if ret else 'off'} | {med(0):.3f} / {med(T//2):.3f} / {med(T-2):.3f} / {med(T-1):.3f} | {coarse} | "
              f"{t0 if not ret else '-'} | {i0[0][4]:.3f} | {i0[0][5]:+.4f} | {resolved}/{len(both)} |")
    print("ceiling violations:", viol, " static width decreasing:", dec)


def scope(zp):
    spec = importlib.util.spec_from_file_location("r22", os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "022", "red_reproduce.py"))
    r22 = importlib.util.module_from_spec(spec); spec.loader.exec_module(r22)
    S = r22.setup(r22.factors(zp)); T = 120
    P, _ = r22.filter_path(S, T)
    G = S["G"]; N = S["N"]
    Sig = [np.diag(G @ P[t] @ G.T + S["Sr"]) for t in range(T + 1)]
    sc = np.array([np.sqrt(np.diag(G @ (P[t] - P[t + 1]) @ G.T)) * Sig[t] / Sig[t + 1] for t in range(T)])   # return units
    print("initial belief-innovation sd (bp): funds median %.2f (range %.2f-%.2f); ETFs %s" % (
        np.median(sc[0, :N]) * 1e4, sc[0, :N].min() * 1e4, sc[0, :N].max() * 1e4, ", ".join(f"{v*1e4:.2f}" for v in sc[0, N:])))
    for kap in (5e-4, 20e-4, 100e-4):
        thr = 2 * kap / np.sqrt(6)
        cross = [next((t for t in range(T) if sc[t, i] < thr), None) for i in range(sc.shape[1])]
        ff = sum(1 for c in cross[:N] if c == 0); fe = sum(1 for c in cross[N:] if c == 0)
        rest = [c for c in cross if c not in (0, None)]
        print(f"kappa {kap*1e4:.0f} bp: threshold {thr*1e4:.2f} bp; funds fine from t=0 {ff}/{N}; ETFs {fe}/{S['M']}; "
              f"latest crossover {max(rest) if rest else '-'}; ETF crossover quarters {cross[N:]}")


if __name__ == "__main__":
    if sys.argv[1] == "scope":
        scope(sys.argv[2]); sys.exit(0)
    keys = [(i, T, k, r) for i in ("etf", "fund") for T in (8, 20) for k in (5e-4, 20e-4, 100e-4) for r in (False, True)]
    with Pool(8) as pool:
        res = pool.map(cell, [k + (1 / 400,) for k in keys])
        res2 = pool.map(cell, [k + (1 / 200,) for k in keys])
    summarize(res, res2)
    for (key, out, sw, lim) in res:
        inst, T, kap, ret, h = key
        if T == 20 and not ret:
            print(f"static width {inst} {kap*1e4:.0f}bp: t=0 {sw[0]:.5f} t=5 {sw[5]:.5f} t=10 {sw[10]:.5f} t=19 {sw[19]:.5f} limit {lim:.5f}")
        if inst == "etf" and kap == 5e-4:
            sh = [np.mean([abs(o[2] * o[3] - o[3]) <= 2 * h + 1e-12 for o in out if o[0] == t]) for t in range(T - 1)]
            print(f"ETF 5bp T={T} returns {'on' if ret else 'off'}: share at ceiling by quarter " + ", ".join(f"{v:.2f}" for v in sh))
