"""Red's reproduction of experiment 022 Part 3 (stationary D13 instance), from the registered Design, without
reading stationary.py: experiment 021's P1 (1 fund, 1 ETF, market factor, caps [0, 1]) with a persistent alpha
alpha_{t+1} = Phi alpha_t + (1 - Phi) abar + eta, stationary alpha SD 0.35%, beliefs at the steady-state Kalman
variance, T = 120, gamma = 5, common kappa. Red's own grid DP (separable L1 distance transform, 20-point
Gauss-Hermite, linear interpolation over 41 belief points at the stationary mean +- 4 stationary sd).

Usage: uv run python experiments/022/red_stationary.py PHI KAPPA_BP
"""
import sys
import numpy as np
LAM, SDF, SDA, SDE, CE, ABAR, SALPHA = 0.0184, 0.0854, 0.02, 0.002, 0.0001, -0.0019, 0.0035

def dt1d(v, k, h):
    out = v.copy()
    for i in range(1, len(v)):
        out[i] = max(out[i], out[i - 1] - k * h)
    for i in range(len(v) - 2, -1, -1):
        out[i] = max(out[i], out[i + 1] - k * h)
    return out

def run(phi, kappa, T=120, gamma=5.0, h=1 / 200, read=(20, 40, 60)):
    q = (1 - phi ** 2) * SALPHA ** 2
    Pm = SALPHA ** 2
    for _ in range(10000):                      # steady-state predictive variance P^- of alpha_t
        Pp = 1 / (1 / Pm + 1 / SDA ** 2); Pm = phi ** 2 * Pp + q
    Pp = 1 / (1 / Pm + 1 / SDA ** 2)
    innov = phi * np.sqrt(Pm - Pp); sd_m = np.sqrt(max(SALPHA ** 2 - Pm, 0))
    n = int(round(1 / h)) + 1; xs = np.linspace(0, 1, n)
    mg = ABAR + np.linspace(-4, 4, 41) * sd_m
    ghx, ghw = np.polynomial.hermite_e.hermegauss(20); ghw = ghw / ghw.sum()
    S = SDF ** 2 * np.ones((2, 2)) + np.diag([SDA ** 2 + Pm, SDE ** 2])
    X1, X2 = np.meshgrid(xs, xs, indexing="ij")
    V = np.zeros((41, n, n)); widths = {}
    idx = np.arange(n)
    for t in reversed(range(T)):
        Vn = np.zeros_like(V); fw = []
        for j, m in enumerate(mg):
            EV = np.zeros((n, n))
            if t < T - 1:
                for z, w in zip(ghx, ghw):
                    mp = np.clip(phi * m + (1 - phi) * ABAR + innov * z, mg[0], mg[-1])
                    k = max(min(np.searchsorted(mg, mp) - 1, 39), 0); a = (mp - mg[k]) / (mg[k + 1] - mg[k])
                    EV += w * ((1 - a) * V[k] + a * V[k + 1])
            mu = np.array([LAM + m, LAM - CE])
            one = mu[0] * X1 + mu[1] * X2 - gamma / 2 * (S[0, 0] * X1 ** 2 + 2 * S[0, 1] * X1 * X2 + S[1, 1] * X2 ** 2)
            Wt = one + EV
            A = np.apply_along_axis(dt1d, 1, Wt, kappa, h)
            Vn[j] = np.apply_along_axis(dt1d, 0, A, kappa, h)
            if t in read:
                it = np.unravel_index(np.argmax(one), one.shape)
                if 0 < it[0] < n - 1:
                    Af = np.max(Wt - kappa * h * np.abs(idx[None, :] - it[1]), axis=1)
                    best = np.argmax(Af[:, None] - kappa * h * np.abs(idx[:, None] - idx[None, :]), axis=0)
                    nt = np.where(best == idx)[0]
                    fw.append((nt.max() - nt.min()) * h if len(nt) else 0.0)
        if t in read:
            widths[t] = (np.median(fw) if fw else float("nan"), len(fw))
        V = Vn
    return innov, sd_m, widths

if __name__ == "__main__":
    phi, kbp = float(sys.argv[1]), float(sys.argv[2])
    innov, sd_m, w = run(phi, kbp * 1e-4)
    print(f"Phi {phi} kappa {kbp} bp: innovation sd {innov * 1e4:.2f} bp, stationary belief sd {sd_m * 1e4:.1f} bp; "
          f"fund median width t=20/40/60: " + " / ".join(f"{w[t][0]:.3f} ({w[t][1]} pts)" for t in (20, 40, 60)))
