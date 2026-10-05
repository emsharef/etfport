"""Grid checks of claim 029 (M6, slack budget): trade-to-edge policy, static width ceiling,
last-review clips, the coarse-regime tilted band, strict narrowing in the fine regime, the
marking brackets, and the two-instrument static parallelotope and Sigma-diameter inequality.

Backward induction on a fine holding grid with linear interpolation; tolerances are a few grid
cells. All inputs are assumed. A check, not a proof. Run: uv run python checks/029/check.py
"""
import sys
import numpy as np

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("FAIL:", msg)


# ---------------------------------------------------------------- one instrument
def solve_1d(inst):
    """Backward induction for one instrument. Returns lo[t][z], hi[t][z] and the policy."""
    grid = inst["grid"]
    n = len(grid)
    feas = grid <= inst["xbar"] + 1e-12
    xf = grid[feas]
    kp, km, c, beta = inst["kp"], inst["km"], inst["c"], inst["beta"]
    T, Z = inst["T"], inst["Z"]
    # cost matrix: rows pre-trade x, columns post-trade x'
    diff = xf[None, :] - grid[:, None]
    cost = kp * np.maximum(diff, 0) + km * np.maximum(-diff, 0)
    V_next = {z: np.zeros(n) for z in range(Z)}
    lo, hi, pol = {}, {}, {}
    for t in range(T - 1, -1, -1):
        V_t = {}
        for z in range(Z):
            xs = inst["xstar"](t, z)
            G = 0.5 * c * (xf - xs) ** 2
            for (z2, g, p) in inst["q"](t, z):
                y = xf * g
                Vn = V_next[z2]
                # linear interpolation; linear extrapolation beyond the grid with the last slope
                v = np.interp(y, grid, Vn)
                over = y > grid[-1]
                if over.any():
                    slope = (Vn[-1] - Vn[-2]) / (grid[-1] - grid[-2])
                    v[over] = Vn[-1] + slope * (y[over] - grid[-1])
                G = G + beta * p * v
            tot = cost + G[None, :]
            arg = np.argmin(tot, axis=1)
            V_t[z] = tot[np.arange(n), arg]
            post = xf[arg]
            nt = np.where(feas & (np.abs(post - grid) < 1e-12))[0]
            lo[(t, z)] = grid[nt.min()]
            hi[(t, z)] = grid[nt.max()]
            pol[(t, z)] = post
        V_next = V_t
    return lo, hi, pol


def check_structure(name, inst, lo, hi, pol):
    grid, dx = inst["grid"], inst["dx"]
    w_static = (inst["kp"] + inst["km"]) / inst["c"]
    for t in range(inst["T"]):
        for z in range(inst["Z"]):
            l, h = lo[(t, z)], hi[(t, z)]
            check(l <= h + 1e-12, f"{name}: lo>hi at t={t} z={z}")
            clip = np.minimum(np.maximum(grid, l), h)
            check(np.max(np.abs(pol[(t, z)] - clip)) <= dx + 1e-12,
                  f"{name}: policy is not clip to the edges at t={t} z={z}")
            check(h - l <= w_static + 2 * dx + 1e-12,
                  f"{name}: width {h-l:.5f} exceeds static width {w_static:.5f} at t={t} z={z}")
    # last review: the clips of 1b
    t = inst["T"] - 1
    for z in range(inst["Z"]):
        xs = inst["xstar"](t, z)
        l_th = min(max(xs - inst["kp"] / inst["c"], 0.0), inst["xbar"])
        h_th = min(max(xs + inst["km"] / inst["c"], 0.0), inst["xbar"])
        check(abs(lo[(t, z)] - l_th) <= dx + 1e-12 and abs(hi[(t, z)] - h_th) <= dx + 1e-12,
              f"{name}: last-review edges ({lo[(t,z)]:.4f},{hi[(t,z)]:.4f}) differ from clips ({l_th:.4f},{h_th:.4f}) at z={z}")


def make_grid(xmax, dx):
    return np.round(np.arange(0.0, xmax + dx / 2, dx), 12)


# A. coarse, symmetric innovations, no marking, symmetric costs: tilt zero inside, +-kappa/c at the ends
def inst_A():
    dx = 0.001
    K = 6

    def xstar(t, z):
        return 0.3 + 0.1 * z

    def q(t, z):
        if z == 0:
            return [(1, 1.0, 1.0)]
        if z == K - 1:
            return [(K - 2, 1.0, 1.0)]
        return [(z - 1, 1.0, 0.5), (z + 1, 1.0, 0.5)]
    return dict(T=4, Z=K, c=1.0, kp=0.01, km=0.01, beta=1.0, xbar=2.0, dx=dx,
                grid=make_grid(2.2, dx), xstar=xstar, q=q)


# B. coarse, skewed mean-zero innovations, asymmetric costs, discounting: nonzero tilt
def inst_B():
    dx = 0.0005
    K = 13  # targets 0.2 + 0.075 z, z = 0..12; up +4 steps (0.3) w.p. 0.2, down 1 step (-0.075) w.p. 0.8

    def xstar(t, z):
        return 0.2 + 0.075 * z

    def q(t, z):
        up, dn = min(z + 4, K - 1), max(z - 1, 0)
        return [(up, 1.0, 0.2), (dn, 1.0, 0.8)]
    return dict(T=4, Z=K, c=1.0, kp=0.012, km=0.008, beta=0.97, xbar=2.0, dx=dx,
                grid=make_grid(2.2, dx), xstar=xstar, q=q, interior=range(1, K - 4))


# C. fine regime: innovations a quarter of the static width
def inst_C():
    dx = 0.0005
    K = 41

    def xstar(t, z):
        return 0.4 + 0.005 * z

    def q(t, z):
        if z == 0:
            return [(1, 1.0, 1.0)]
        if z == K - 1:
            return [(K - 2, 1.0, 1.0)]
        return [(z - 1, 1.0, 0.5), (z + 1, 1.0, 0.5)]
    return dict(T=6, Z=K, c=1.0, kp=0.01, km=0.01, beta=1.0, xbar=2.0, dx=dx,
                grid=make_grid(1.0, dx), xstar=xstar, q=q)


# D. marking: gross returns 0.9 or 1.1, constant target
def inst_D():
    dx = 0.0005
    return dict(T=3, Z=1, c=1.0, kp=0.01, km=0.01, beta=1.0, xbar=2.0, dx=dx,
                grid=make_grid(2.5, dx), xstar=lambda t, z: 0.5,
                q=lambda t, z: [(0, 0.9, 0.5), (0, 1.1, 0.5)])


# E. a binding cap on instance A's law
def inst_E():
    d = inst_A()
    d["xbar"] = 0.505
    d["xstar"] = lambda t, z: 0.5 + 0.1 * (z - 2)
    d["grid"] = make_grid(1.0, d["dx"])
    return d


def run_1d():
    for name, mk in (("A", inst_A), ("B", inst_B), ("C", inst_C), ("D", inst_D), ("E", inst_E)):
        inst = mk()
        lo, hi, pol = solve_1d(inst)
        check_structure(name, inst, lo, hi, pol)
        dx, c, kp, km, beta = inst["dx"], inst["c"], inst["kp"], inst["km"], inst["beta"]
        w_static = (kp + km) / c
        if name in ("A", "B"):
            # coarse regime (1d): every innovation exceeds (1+beta)(kp+km)/c, edges interior
            states = inst.get("interior", range(inst["Z"]))
            for t in range(inst["T"] - 1):
                for z in states:
                    xs = inst["xstar"](t, z)
                    U = sum(p * g for (z2, g, p) in inst["q"](t, z) if inst["xstar"](t + 1, z2) > xs)
                    D = sum(p * g for (z2, g, p) in inst["q"](t, z) if inst["xstar"](t + 1, z2) < xs)
                    for (z2, g, p) in inst["q"](t, z):
                        check(abs(inst["xstar"](t + 1, z2) - xs) >= (1 + beta) * w_static,
                              f"{name}: instance is not coarse at t={t} z={z}")
                    tau = beta * (kp * U - km * D) / c
                    h_th, l_th = xs + km / c + tau, xs - kp / c + tau
                    check(abs(hi[(t, z)] - h_th) <= 2 * dx and abs(lo[(t, z)] - l_th) <= 2 * dx,
                          f"{name}: coarse edges ({lo[(t,z)]:.5f},{hi[(t,z)]:.5f}) differ from tilted static band ({l_th:.5f},{h_th:.5f}) at t={t} z={z}, tilt {tau:.5f}")
                    check(abs((hi[(t, z)] - lo[(t, z)]) - w_static) <= 2 * dx,
                          f"{name}: coarse width {hi[(t,z)]-lo[(t,z)]:.5f} is not the static width at t={t} z={z}")
            if name == "B":
                tilts = {beta * (kp * 0.2 - km * 0.8) / c}
                check(all(abs(x) > 3 * dx for x in tilts), "B: the skewed tilt is not resolved by the grid")
        if name == "C":
            for t in range(inst["T"] - 1):
                for z in range(10, 31):
                    w = hi[(t, z)] - lo[(t, z)]
                    check(w < w_static - 4 * dx,
                          f"C: fine-regime width {w:.5f} not strictly below static {w_static:.5f} at t={t} z={z}")
            # the T-2 band of the fine instance is computed by hand in the claim's check design: half the static width
            w = hi[(inst["T"] - 2, 20)] - lo[(inst["T"] - 2, 20)]
            check(abs(w - 0.5 * w_static) <= 3 * dx, f"C: T-2 width {w:.5f} is not half the static width")
        if name == "D":
            gbar = 1.0
            for t in range(inst["T"]):
                l_b = min(inst["xbar"], 0.5 - (kp + beta * km * gbar) / c)
                h_b = max(0.0, 0.5 + (km + beta * kp * gbar) / c)
                check(lo[(t, 0)] >= l_b - 2 * dx and hi[(t, 0)] <= h_b + 2 * dx,
                      f"D: edge brackets violated at t={t}: lo={lo[(t,0)]:.5f} (>= {l_b:.5f}), hi={hi[(t,0)]:.5f} (<= {h_b:.5f})")
        print(f"instance {name}: ok  (widths at t=0: " +
              ", ".join(f"{hi[(0,z)]-lo[(0,z)]:.4f}" for z in range(min(inst['Z'], 5))) + " ...)")


# ---------------------------------------------------------------- two instruments
def run_2d():
    gamma = 1.0
    Sig = np.array([[1.0, 0.5], [0.5, 1.0]])
    kp = np.array([0.010, 0.006])
    km = np.array([0.008, 0.006])
    xs = np.array([0.5, 0.4])
    dx = 0.0025
    g1 = np.round(np.arange(0.40, 0.60 + dx / 2, dx), 12)
    g2 = np.round(np.arange(0.30, 0.50 + dx / 2, dx), 12)
    X = np.array([(a, b) for a in g1 for b in g2])  # states = actions (box far from bounds)
    m = len(X)
    D = X - xs
    quad = 0.5 * gamma * np.einsum("ij,jk,ik->i", D, Sig, D)
    T = 2
    V_next = np.zeros(m)
    NT = {}
    for t in (1, 0):
        G = quad + V_next  # no marking, constant target, beta = 1
        V_t = np.empty(m)
        nt = np.zeros(m, dtype=bool)
        for i in range(m):
            diff = X - X[i]
            cost = (kp * np.maximum(diff, 0) + km * np.maximum(-diff, 0)).sum(axis=1)
            tot = cost + G
            j = int(np.argmin(tot))
            V_t[i] = tot[j]
            nt[i] = (j == i)
        NT[t] = nt
        V_next = V_t
    # 2c at T-1: parallelotope, with a grid margin
    grad = gamma * (D @ Sig)
    margin = gamma * np.abs(Sig).sum(axis=1).max() * dx
    inside = np.all((grad >= -kp + margin) & (grad <= km - margin), axis=1)
    outside = np.any((grad < -kp - margin) | (grad > km + margin), axis=1)
    check(np.all(NT[1][inside]), "2D: a point strictly inside the static parallelotope trades at T-1")
    check(not np.any(NT[1][outside]), "2D: a point strictly outside the static parallelotope does not trade at T-1")
    check(NT[1].sum() > 20 and NT[0].sum() > 5, "2D: no-trade sets too small to test")
    # 2b at both dates
    for t in (1, 0):
        P = X[NT[t]]
        Dp = P[:, None, :] - P[None, :, :]
        lhs = gamma * np.einsum("abj,jk,abk->ab", Dp, Sig, Dp)
        rhs = (np.abs(Dp) * (kp + km)).sum(axis=2)
        # the discrete no-trade set extends up to one cell beyond the exact one; allow that
        tol = 2 * gamma * np.abs(Sig).sum(axis=1).max() * dx * np.abs(Dp).sum(axis=2)
        check(np.all(lhs <= rhs + tol + 1e-12), f"2D: Sigma-diameter inequality fails at t={t}")
    # the bundling shift: fund A's static band centre moves with the ETF deviation
    dA = D[NT[1], 0]; dE = D[NT[1], 1]
    shift_th = -Sig[0, 1] * dE / Sig[0, 0]
    check(np.all(dA >= shift_th - kp[0] / (gamma * Sig[0, 0]) - dx - 1e-12) and
          np.all(dA <= shift_th + km[0] / (gamma * Sig[0, 0]) + dx + 1e-12),
          "2D: fund coordinate of the static no-trade set is not the shifted static interval")
    print(f"2D: ok  (no-trade points: T-1 {NT[1].sum()}, T-2 {NT[0].sum()})")


if __name__ == "__main__":
    run_1d()
    run_2d()
    if FAIL:
        print(f"{len(FAIL)} check(s) failed")
        sys.exit(1)
    print("all checks passed")
