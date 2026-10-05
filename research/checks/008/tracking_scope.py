"""Fixed exact M2 scope checks for red's claim 008 objection; no optimizer.

Run: uv run python checks/008/tracking_scope.py
Inputs are assumed. This supplements the paper calculations; it is not a proof.
"""
from fractions import Fraction as F
from itertools import product

SIGNS = tuple(product((-1, 1), repeat=3))
MASS = F(1, 8)
MEAN = F(1, 50)


def average(values):
    return sum(MASS * value for value in values)


def cross(xs, ys):
    return average([x * y for x, y in zip(xs, ys)])


def main():
    factor = [F(s, 10) for s, _, _ in SIGNS]
    active_residual = [F(s, 100) for _, s, _ in SIGNS]
    etf_residual = [F(s, 100) for _, _, s in SIGNS]
    active = [f + z for f, z in zip(factor, active_residual)]
    etf = [f + z for f, z in zip(factor, etf_residual)]
    assert all(average(xs) == 0 for xs in (factor, active_residual, etf_residual))
    assert cross(active_residual, etf_residual) == 0
    assert cross(factor, active_residual) == cross(factor, etf_residual) == 0
    assert min(1 + MEAN + x for x in active + etf) == F(91, 100)
    sigma = [[cross(x, y) for y in (active, etf)] for x in (active, etf)]
    assert sigma == [[F(101, 10000), F(1, 100)], [F(1, 100), F(101, 10000)]]
    epsilon = [a - e for a, e in zip(active, etf)]
    assert cross(etf, epsilon) == F(-1, 10000)

    def score(a, p):
        gains = [a * (MEAN + x) + p * (MEAN + y) for x, y in zip(active, etf)]
        mean = average(gains)
        variance = average([(g - mean) ** 2 for g in gains])
        return mean - variance / 2

    # Independent global certificate: common positive marginal at the funded
    # full candidate, positive definite Sigma; E has a positive ETF marginal.
    w = (F(1, 2), F(1, 2))
    g = [MEAN - sum(row[j] * w[j] for j in range(2)) for row in sigma]
    assert g == [F(199, 20000)] * 2
    assert sum(w) == 1 and g[0] > 0
    assert sigma[0][0] > 0 and sigma[0][0] * sigma[1][1] - sigma[0][1] ** 2 > 0
    assert MEAN - sigma[1][1] > 0
    assert score(*w) == F(599, 40000)
    assert score(F(0), F(1)) == F(299, 20000)
    assert score(*w) - score(F(0), F(1)) == F(1, 40000)
    for a, p in ((F(0), F(0)), w, (F(1), F(0)), (F(1, 3), F(1, 4))):
        t = a + p
        assert score(a, p) == t / 50 - F(201, 40000) * t ** 2 - (a - p) ** 2 / 40000
    print("PASS: independent residuals, noisy ETF, unique full optimum and positive class gap")

    # Shared residual noise: claim 008 does not require a noiseless ETF in M2.
    shared_active_residual = [z + e for z, e in zip(etf_residual, active_residual)]
    shared_active = [f + z for f, z in zip(factor, shared_active_residual)]
    shared_epsilon = [a - e for a, e in zip(shared_active, etf)]
    assert cross(etf_residual, etf_residual) > 0
    assert cross(etf, shared_epsilon) == 0
    assert cross(shared_epsilon, shared_epsilon) > 0
    assert all(1 + MEAN + x > 0 for x in shared_active)
    print("PASS: a noisy ETF can satisfy the hypothesis when residual noise is shared")


if __name__ == "__main__":
    main()
