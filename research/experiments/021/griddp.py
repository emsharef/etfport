"""Experiment 021: grid dynamic programming on (x_-, m) for instances with one moving belief coordinate (alpha_1).

Holdings lie on a tensor grid (one axis per instrument); the moving belief mean m (alpha_1's posterior mean) lies on
a 41-point grid m_0 +- 4 sd(m_T - m_0). With W_t(y, m) = y'mu(m) - (gamma/2) y'S_t y + E V_{t+1}(y, m'), the
Bellman step is V_t(x, m) = max_y [W_t(y, m) - C(y - x)] over the holdings grid. C is separable across instruments,
so the maximization is done one axis at a time:
- proportional C (kappa |v|): an exact one-dimensional L1 distance transform (forward and backward passes);
- quadratic C ((Lambda/2) v^2): brute force along the axis.
Ties are broken toward no trade. The expectation over m' = m + sqrt(Q_t) z uses 20-point Gauss-Hermite nodes with
linear interpolation in m (clamped at the grid ends). Values are grid-restricted: actions lie on the grid.
"""
import numpy as np

GH_Z, GH_W = np.polynomial.hermite_e.hermegauss(20)
GH_W = GH_W / GH_W.sum()


def l1_transform(W, kappa_h, axis):
    """U(x) = max_y W(y) - kappa |y - x| along `axis` on a uniform grid (kappa_h = kappa * step). Returns U, argmax."""
    W = np.moveaxis(W, axis, -1)
    G = W.shape[-1]
    g = W.copy(); a = np.broadcast_to(np.arange(G), W.shape).copy()
    for i in range(1, G):
        cand = g[..., i - 1] - kappa_h
        better = cand > g[..., i]
        g[..., i] = np.where(better, cand, g[..., i]); a[..., i] = np.where(better, a[..., i - 1], a[..., i])
    for i in range(G - 2, -1, -1):
        cand = g[..., i + 1] - kappa_h
        better = cand > g[..., i]
        g[..., i] = np.where(better, cand, g[..., i]); a[..., i] = np.where(better, a[..., i + 1], a[..., i])
    return np.moveaxis(g, -1, axis), np.moveaxis(a, -1, axis)


def quad_transform(W, lam_half, xs, axis, chunk=2000):
    """U(x) = max_y W(y) - lam_half (y - x)^2 along `axis`, brute force. Returns U, argmax."""
    W = np.moveaxis(W, axis, -1)
    shp = W.shape
    Wf = W.reshape(-1, shp[-1])
    pen = lam_half * (xs[None, :] - xs[:, None]) ** 2          # [y, x]
    U = np.empty_like(Wf); A = np.empty(Wf.shape, dtype=int)
    for s in range(0, Wf.shape[0], chunk):
        blk = Wf[s:s + chunk][:, :, None] - pen[None, :, :]     # [row, y, x]
        A[s:s + chunk] = blk.argmax(axis=1)
        U[s:s + chunk] = np.take_along_axis(blk, A[s:s + chunk][:, None, :], 1)[:, 0, :]
    return np.moveaxis(U.reshape(shp), -1, axis), np.moveaxis(A.reshape(shp), -1, axis)


def solve(I, grids, cost, kind, mgrid, keep_policy=True):
    """grids: list of 1-D holdings grids (uniform); cost: per-instrument kappa or Lambda; kind 'l1' or 'quad'.
    Returns V_0 on (x..., m), and per t the argmax index arrays (one per instrument) if keep_policy."""
    n = I.n
    X = np.meshgrid(*grids, indexing="ij")                  # n arrays of shape G1 x ... x Gn
    xs_flat = np.stack([x.ravel() for x in X], axis=1)       # (P, n)
    m0 = I.m0()
    Hm = I.H()
    V_next = np.zeros(X[0].shape + (len(mgrid),))
    policies = [None] * I.T
    for t in reversed(range(I.T)):
        S = I.S(t)
        quad = -0.5 * I.gamma * np.einsum("pi,ij,pj->p", xs_flat, S, xs_flat).reshape(X[0].shape)
        W = np.empty_like(V_next)
        q = np.sqrt(I.Q(t)[0, 0])                                 # innovation sd of alpha_1's mean
        for j, mv in enumerate(mgrid):
            m = m0.copy(); m[0] = mv
            mu = Hm @ m + I.g0()
            lin = (xs_flat @ mu).reshape(X[0].shape)
            if t == I.T - 1:
                ev = 0.0
            else:
                ev = 0.0
                for z, w in zip(GH_Z, GH_W):
                    mp = np.clip(mv + q * z, mgrid[0], mgrid[-1])
                    k = min(np.searchsorted(mgrid, mp) - 1, len(mgrid) - 2); k = max(k, 0)
                    th = (mp - mgrid[k]) / (mgrid[k + 1] - mgrid[k])
                    ev = ev + w * ((1 - th) * V_next[..., k] + th * V_next[..., k + 1])
            W[..., j] = lin + quad + ev
        # Bellman step: axis by axis, last instrument first
        U, args = W, []
        for ax in reversed(range(n)):
            h = grids[ax][1] - grids[ax][0]
            if kind == "l1":
                U, A = l1_transform(U, cost[ax] * h, ax)
            else:
                U, A = quad_transform(U, 0.5 * cost[ax], grids[ax], ax)
            args.append((ax, A))
        V_next = U
        if keep_policy:
            policies[t] = compose(args, X[0].shape + (len(mgrid),), n)
    return V_next, policies


def compose(args, shape, n):
    """Turn the per-axis argmax arrays into the optimal y index for every instrument at every state."""
    # Axes were transformed last-first, so the array for axis ax is indexed by (y_0..y_{ax-1}, x_ax..x_{n-1}, m).
    # Resolve from axis 0 (transformed last, indexed by x only) inward, substituting each y as it is found.
    idx = np.indices(shape)
    y = [None] * n
    order = {ax: A for ax, A in args}
    cur = list(idx)                        # current index tuple used to look up each array
    for ax in range(n):
        A = order[ax]
        yax = A[tuple(cur)]
        y[ax] = yax
        cur[ax] = yax                      # later axes' arrays are indexed by y_ax in position ax
    return np.stack(y)
