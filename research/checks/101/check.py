"""Evidence around refuted claim 101 (M7, Gaussian law, one fund, one factor, pure-learning marking, beta = 1).

Claim 101 was refuted by red: its half-width constant was 8 where the heuristic and the benchmarks give 4.
This script now prints red's corrected 2 Delta* (constant 4) and the root-six crossover; the record of the
refutation is claims/refuted/101 and the ROADMAP D13 answer. The corrected form is a cited result, not a claim.

Deviation-from-target dynamic programming with Gauss-Hermite quadrature along the fixed-means Kalman
path; prints the band width against the conjectured 2 Delta_t and against the static width, and the
centre displacement against the conjectured drift displacement. Asserts only the exact ceiling of
claim 029/100 and internal consistency. All inputs are assumed. A check, not a proof.
Run: uv run python checks/101/check.py
"""
import sys
import numpy as np

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


# ------------------------------------------------------------ assumed instance and filter path
b = 1.0
sf, sA = 0.06, 0.03
m0 = np.array([0.02, 0.004])
P0 = np.diag([0.012**2, 0.006**2])
H = np.array([[1.0, 0.0], [b, 1.0]])
L = np.array([[1.0, 0.0], [b, 1.0]])
Sz = np.diag([sf**2, sA**2])
R = L @ Sz @ L.T
G = np.array([b, 1.0])
Sr = b * b * sf**2 + sA**2
gamma = 3.0
T = 120
Rinv = np.linalg.inv(R)
Minfo = np.linalg.inv(H.T @ Rinv @ H)
P = [np.linalg.inv(np.linalg.inv(P0) + t * H.T @ Rinv @ H) for t in range(T + 2)]
Sig = [float(G @ P[t] @ G) + Sr for t in range(T + 2)]
c = [gamma * s for s in Sig]
V = [P[t] - P[t + 1] for t in range(T + 1)]
v = [float(G @ V[t] @ G) / (gamma * Sig[t + 1]) ** 2 for t in range(T + 1)]   # target innovation variance
s = [np.sqrt(x) for x in v]
mu0 = float(G @ m0)
xstar0 = [mu0 / (gamma * Sig[t]) for t in range(T + 2)]                    # target at the prior mean
delta = [xstar0[t] * (Sig[t] / Sig[t + 1] - 1.0) for t in range(T + 1)]   # learning drift (frozen at prior mean)

# Gauss-Hermite nodes for a standard normal
gh_x, gh_w = np.polynomial.hermite_e.hermegauss(16)
gh_w = gh_w / gh_w.sum()

# ------------------------------------------------------------ deviation DP
dx = 0.001
D = 2.0
grid = np.round(np.arange(-D, D + dx / 2, dx), 12)
n = len(grid)
diff = grid[None, :] - grid[:, None]   # rows: pre-trade deviation, cols: post-trade deviation


def run(name, kp, km):
    cost = kp * np.maximum(diff, 0) + km * np.maximum(-diff, 0)
    Vn = np.zeros(n)
    lo_n = hi_n = None
    rows = {}
    wid = {}
    for t in range(T - 1, -1, -1):
        Gv = 0.5 * c[t] * grid ** 2
        # next deviation: d' = d - (x*_{t+1} - x*_t) = d - delta_t - s_t * xi
        cont = np.zeros(n)
        for xk, wk in zip(gh_x, gh_w):
            y = grid - delta[t] - s[t] * xk
            val = np.interp(y, grid, Vn)
            if lo_n is not None:
                below = y < grid[0]
                above = y > grid[-1]
                # exact affine extrapolation outside the (next) band
                val[below] = Vn[0] + kp * (grid[0] - y[below])
                val[above] = Vn[-1] + km * (y[above] - grid[-1])
            cont += wk * val
        Gv = Gv + cont
        tot = cost + Gv[None, :]
        arg = np.argmin(tot, axis=1)
        Vt = tot[np.arange(n), arg]
        post = grid[arg]
        nt = np.where(np.abs(post - grid) < 1e-12)[0]
        lo, hi = grid[nt.min()], grid[nt.max()]
        clip = np.minimum(np.maximum(grid, lo), hi)
        check(np.max(np.abs(post - clip)) <= dx + 1e-12, f"{name}: policy not a clip at t={t}")
        check(lo > grid[0] + 10 * dx and hi < grid[-1] - 10 * dx, f"{name}: band touches the grid edge at t={t}")
        w_static = (kp + km) / c[t]
        check(hi - lo <= w_static + 2 * dx + 1e-12, f"{name}: width {hi-lo:.4f} above static {w_static:.4f} at t={t}")
        wid[t] = (lo, hi)
        Vn, lo_n, hi_n = Vt, lo, hi
    # report
    print(f"\n{name}: kappa+ = {kp*1e4:.0f} bp, kappa- = {km*1e4:.0f} bp")
    tc = next((t for t in range(T) if np.sqrt(6.0) * s[t] * c[t] < kp + km), None)
    print(f"  crossover quarter (s_t < w_t/sqrt6): t_c = {tc}")
    print("   t   width   2Delta   width/2Delta   width/static   centre-x*   (2/3)(delta/v)Delta^2   tau_mix")
    for t in (1, 5, 10, 20, 40, 60, 80, 100):
        lo, hi = wid[t]
        Delta = (3 * (kp + km) * v[t] / (4 * c[t])) ** (1 / 3)
        w_static = (kp + km) / c[t]
        shift_th = (2 / 3) * (delta[t] / v[t]) * Delta ** 2
        tau = Delta ** 2 / v[t]
        print(f"  {t:3d}  {hi-lo:7.4f}  {2*Delta:7.4f}   {(hi-lo)/(2*Delta):8.3f}      {(hi-lo)/w_static:7.3f}     {(hi+lo)/2:+8.4f}   {shift_th:+10.5f}         {tau:7.1f}")
    return wid


run("fund-like", 0.005, 0.005)
run("ETF-like", 0.0005, 0.0005)

if FAIL:
    print(f"{len(FAIL)} check(s) failed")
    sys.exit(1)
print("all checks passed (exact ceiling and clip structure); the tables compare the band with red's corrected 2 Delta*, a cited result")
