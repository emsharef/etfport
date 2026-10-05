"""Experiment 023: a vectorized exact L1 conjugate on a uniform grid, with directional rates.

U(x) = max_y [ W(y) - kp (y - x)^+ - km (x - y)^+ ] along one axis, where kp and km are the purchase and sale rates
times the grid step (per grid index). Split y <= x (sell) and y >= x (buy):
    sell: max_{j <= i} W_j + km j  - km i      (running maximum from the left)
    buy:  max_{j >= i} W_j - kp j  + kp i      (running maximum from the right)
The argmax is the maximizing j closest to i, so ties go to the smaller trade and to no trade when W_i itself attains
the maximum. This is the same transform as experiment 021's l1_transform (there kp = km), computed with cumulative
maxima instead of a loop.
"""
import numpy as np


def _run_argmax(A, axis):
    """Running maximum along axis and the last index attaining it (ties toward the current position)."""
    M = np.maximum.accumulate(A, axis=axis)
    idx = np.arange(A.shape[axis]).reshape([-1 if a == axis % A.ndim else 1 for a in range(A.ndim)])
    last = np.where(A == M, idx, 0)
    return M, np.maximum.accumulate(last, axis=axis)


def l1(W, kp, km, axis):
    W = np.moveaxis(W, axis, -1)
    G = W.shape[-1]
    j = np.arange(G)
    # sell side: y = j <= i
    Ms, As = _run_argmax(W + km * j, -1)
    sell = Ms - km * j
    # buy side: y = j >= i, running max from the right
    Wr = (W - kp * j)[..., ::-1]
    Mb, Ab = _run_argmax(Wr, -1)
    buy = Mb[..., ::-1] + kp * j
    Ab = (G - 1 - Ab)[..., ::-1]
    U = np.maximum(sell, buy)
    # prefer the side whose argmax is nearer i (no trade when both are i)
    A = np.where(buy > sell, Ab, np.where(sell > buy, As, np.where(np.abs(As - j) <= np.abs(Ab - j), As, Ab)))
    return np.moveaxis(U, -1, axis), np.moveaxis(A, -1, axis)
