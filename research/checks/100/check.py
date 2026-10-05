"""Checks of claim 100 (M7, finite-law variant, one fund, one factor, pure-learning marking).

The linear filter is run on the whole observation tree; the band is computed by claim 029's grid
dynamic programming with the time-varying curvature c_t = gamma Sigma_t. Tolerances are a few grid
cells. All inputs are assumed. A check, not a proof. Run: uv run python checks/100/check.py
"""
import sys
import itertools
import numpy as np

FAIL = []


def sc(a):
    return float(np.asarray(a).reshape(-1)[0])


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


# ------------------------------------------------------------ assumed instance
b = 1.0                      # fund loading on the single factor
sf, sA = 0.06, 0.03          # shock scales: factor and residual (per quarter)
m0 = np.array([0.02, 0.004])  # prior mean of (lambda, alpha)
s_l, s_a = 0.012, 0.006      # prior standard deviations (finite two-point priors)
P0 = np.diag([s_l**2, s_a**2])
H = np.array([[1.0, 0.0], [b, 1.0]])
L = np.array([[1.0, 0.0], [b, 1.0]])
Sz = np.diag([sf**2, sA**2])
R = L @ Sz @ L.T
G = np.array([[b, 1.0]])
Sr = b * b * sf**2 + sA**2
gamma = 3.0
beta = 1.0
T = 5

# finite laws: theta in the four corners, shocks in the four sign combinations
thetas = [np.array([m0[0] + i * s_l, m0[1] + j * s_a]) for i in (-1, 1) for j in (-1, 1)]
shocks = [np.array([i * sf, j * sA]) for i in (-1, 1) for j in (-1, 1)]

# ------------------------------------------------------------ deterministic filter path
P = [P0]
K = []
for t in range(T):
    S = H @ P[t] @ H.T + R
    Kt = P[t] @ H.T @ np.linalg.inv(S)
    K.append(Kt)
    P.append(P[t] - Kt @ H @ P[t])
Sig = [sc(G @ P[t] @ G.T) + Sr for t in range(T + 1)]
c = [gamma * s for s in Sig]
V = [P[t] - P[t + 1] for t in range(T)]

# information form and monotonicity (2a)
for t in range(T + 1):
    info = np.linalg.inv(P0) + t * H.T @ np.linalg.inv(R) @ H
    check(np.allclose(np.linalg.inv(info), P[t], atol=1e-12), f"information form fails at t={t}")
    if t < T:
        ev = np.linalg.eigvalsh(P[t] - P[t + 1])
        check(ev.min() >= -1e-14, f"P not nonincreasing at t={t}")
        check(Sig[t + 1] <= Sig[t] + 1e-14, f"Sigma not nonincreasing at t={t}")
check(all(c[t + 1] <= c[t] + 1e-15 for t in range(T - 1)), "curvature not nonincreasing (static width not nondecreasing)")

# ------------------------------------------------------------ the observation tree
# a node is a history of (theta index, shock index) pairs; the public state is the shock-observed y's
# y = H theta + L z, so distinct (theta, z) pairs may give the same y; group by y to build the public tree
def obs(theta, z):
    return tuple(np.round(H @ theta + L @ z, 12))


def m_after(m, Pt, y):
    Kt = P_gain(Pt)
    return m + Kt @ (y - H @ m)


def P_gain(Pt):
    return Pt @ H.T @ np.linalg.inv(H @ Pt @ H.T + R)


# enumerate public histories with their joint masses over theta
# state: dict history -> list of (theta index, mass)
prior_mass = 1.0 / len(thetas)
shock_mass = 1.0 / len(shocks)
level = {(): [(k, prior_mass) for k in range(len(thetas))]}
levels = [level]
for t in range(T):
    nxt = {}
    for hist, posts in level.items():
        for k, mass in posts:
            for z in shocks:
                y = obs(thetas[k], z)
                nxt.setdefault(hist + (y,), []).append((k, mass * shock_mass))
    # merge equal theta indices
    for h in nxt:
        d = {}
        for k, mass in nxt[h]:
            d[k] = d.get(k, 0.0) + mass
        nxt[h] = sorted(d.items())
    levels.append(nxt)
    level = nxt

# filter means along histories
def mean_of(hist):
    m = m0.copy()
    for t, y in enumerate(hist):
        m = m + K[t] @ (np.array(y) - H @ m)
    return m


# 2b: unconditional innovation covariance equals V_t; drift sign
for t in range(T):
    cov = np.zeros((2, 2)); mean = np.zeros(2)
    for hist, posts in levels[t + 1].items():
        mass = sum(mm for _, mm in posts)
        eps = mean_of(hist) - mean_of(hist[:-1])
        mean += mass * eps
        cov += mass * np.outer(eps, eps)
    check(np.allclose(mean, 0, atol=1e-12), f"innovation mean not zero at t={t}")
    check(np.allclose(cov, V[t], atol=1e-12), f"innovation covariance differs from P_t - P_(t+1) at t={t}")
    for hist in levels[t]:
        mu = sc(G @ mean_of(hist))
        drift = mu * (1 / Sig[t + 1] - 1 / Sig[t]) / gamma
        check(drift * mu >= 0, f"drift sign differs from mu at t={t}")
        xs_next = {}
        for hist2, posts in levels[t + 1].items():
            if hist2[:-1] != hist:
                continue
            eps = mean_of(hist2) - mean_of(hist)
            lhs = sc(G @ mean_of(hist2)) / (gamma * Sig[t + 1]) - mu / (gamma * Sig[t])
            rhs = sc(G @ eps) / (gamma * Sig[t + 1]) + drift
            check(abs(lhs - rhs) < 1e-12, f"target decomposition fails at t={t}")
print("filter path: ok  (curvatures " + ", ".join(f"{x:.5f}" for x in c) + ")")

# ------------------------------------------------------------ band by grid DP over the tree (pure learning)
dx = 0.0005
xbar = 3.0
grid = np.round(np.arange(0.0, xbar + 0.4 + dx / 2, dx), 12)
feas = grid <= xbar + 1e-12
xf = grid[feas]
n = len(grid)
diff = xf[None, :] - grid[:, None]


def xstar(t, hist):
    return sc(G @ mean_of(hist)) / (gamma * Sig[t])


def trans(t, hist):
    """public transition law: histories at t+1 extending hist, with conditional masses"""
    tot = sum(mm for _, mm in levels[t][hist])
    out = []
    for hist2, posts in levels[t + 1].items():
        if hist2[:-1] == hist:
            out.append((hist2, sum(mm for _, mm in posts) / tot))
    return out


def run_bands(name, kp, km, expect_coarse):
    cost = kp * np.maximum(diff, 0) + km * np.maximum(-diff, 0)
    w_static = [(kp + km) / c[t] for t in range(T)]
    V_next = {hist: np.zeros(n) for hist in levels[T]}
    lo, hi, xs_at = {}, {}, {}
    for t in range(T - 1, -1, -1):
        V_t = {}
        for hist in levels[t]:
            xs = xstar(t, hist)
            xs_at[(t, hist)] = xs
            Gv = 0.5 * c[t] * (xf - xs) ** 2
            for hist2, p in trans(t, hist):
                Gv = Gv + beta * p * np.interp(xf, grid, V_next[hist2])
            tot = cost + Gv[None, :]
            arg = np.argmin(tot, axis=1)
            V_t[hist] = tot[np.arange(n), arg]
            post = xf[arg]
            nt = np.where(feas & (np.abs(post - grid) < 1e-12))[0]
            lo[(t, hist)] = grid[nt.min()]
            hi[(t, hist)] = grid[nt.max()]
            clip = np.minimum(np.maximum(grid, lo[(t, hist)]), hi[(t, hist)])
            check(np.max(np.abs(post - clip)) <= dx + 1e-12, f"{name}: policy not a clip at t={t}")
        V_next = V_t

    n_static, n_coarse, n_narrow, n_tilt = 0, 0, 0, 0
    for t in range(T):
        for hist in levels[t]:
            l, h = lo[(t, hist)], hi[(t, hist)]
            xs = xs_at[(t, hist)]
            w = h - l
            check(w <= w_static[t] + 2 * dx + 1e-12, f"{name}: width {w:.5f} above static {w_static[t]:.5f} at t={t}")
            if t == T - 1:
                check(abs(l - min(max(xs - kp / c[t], 0), xbar)) <= dx + 1e-12 and abs(h - min(max(xs + km / c[t], 0), xbar)) <= dx + 1e-12,
                      f"{name}: last-review clip fails at t={t}")
                continue
            moves = [(xs_at[(t + 1, h2)] - xs, p) for h2, p in trans(t, hist)]
            U = sum(p for mv, p in moves if mv > 0)
            D = sum(p for mv, p in moves if mv < 0)
            thresh = (km + beta * kp) / c[t] + (kp + beta * km) / c[t + 1]
            if abs(w - w_static[t]) <= 2 * dx and l > 0 and h < xbar:
                n_static += 1
                # 2d: side-weight move bound at a static-width band
                for mv, p in moves:
                    if mv > 0:
                        bound = (km * (1 - beta) + beta * (kp + km) * U) / c[t]
                        check(mv >= bound - 4 * dx, f"{name}: up move {mv:.5f} below bound {bound:.5f} at t={t}")
                    elif mv < 0:
                        bound = (kp * (1 - beta) + beta * (kp + km) * D) / c[t]
                        check(-mv >= bound - 4 * dx, f"{name}: down move {-mv:.5f} below bound {bound:.5f} at t={t}")
                    else:
                        check(False, f"{name}: zero target move at a static-width band, t={t}")
            if all(abs(mv) > thresh for mv, p in moves) and l > 0 and h < xbar:
                n_coarse += 1
                tau = beta * (kp * U - km * D) / c[t]
                check(abs(h - (xs + km / c[t] + tau)) <= 2 * dx and abs(l - (xs - kp / c[t] + tau)) <= 2 * dx,
                      f"{name}: coarse edges differ from tilted static band at t={t} (tilt {tau:.5f})")
                # 2c: with symmetric costs the tilt has the sign of the drift (= sign of mu) when U != D
                mu = sc(G @ mean_of(hist))
                if abs(U - D) > 1e-9:
                    n_tilt += 1
                    check(tau * mu > 0, f"{name}: tilt sign differs from the drift's at t={t}")
            if w < w_static[t] - 4 * dx:
                n_narrow += 1
    late = all(hi[(T - 2, h)] - lo[(T - 2, h)] < w_static[T - 2] - 4 * dx for h in levels[T - 2])
    if expect_coarse:
        check(n_coarse > 0 and n_static > 0, f"{name}: instance meant to have coarse quarters has none")
    else:
        check(late, f"{name}: T-2 bands are not all strictly narrower than the static width")
    print(f"{name}: ok  (static widths {w_static[0]:.4f}..{w_static[-1]:.4f}; static-width bands {n_static}, coarse checks {n_coarse}, tilt-sign checks {n_tilt}, strictly narrow {n_narrow}, T-2 all narrow {late})")


run_bands("fine (40 bp each way)", 0.004, 0.004, expect_coarse=False)
run_bands("coarse start (2 bp each way)", 0.0002, 0.0002, expect_coarse=True)

if FAIL:
    print(f"{len(FAIL)} check(s) failed")
    sys.exit(1)
print("all checks passed")
