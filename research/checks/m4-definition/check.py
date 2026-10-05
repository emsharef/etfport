"""Exact finite definition checks for proposed M4, not its coverage theorem.

Run: uv run python checks/m4-definition/check.py (repository uv.lock).
Checks joint covariance, singular directions, finite quantile atoms, and recovery
of the specified estimator from public returns. No statistical simulation/results.
"""
from collections import defaultdict
from itertools import product

from sympy import Matrix, Rational as Q, zeros


def calibration(noises, count=2, eta=Q(1, 4)):
    dimension = noises[0].rows
    omega = sum((z * z.T for z in noises), zeros(dimension)) / len(noises)
    inverse = omega.pinv()
    mass = defaultdict(lambda: Q(0))
    histories = list(product(noises, repeat=count))
    errors = []
    for history in histories:
        error = sum(history, zeros(dimension, 1)) / count
        assert omega * inverse * error == error
        statistic = (count * error.T * inverse * error)[0]
        mass[statistic] += Q(1, len(histories))
        errors.append(error)
    cumulative = Q(0)
    for critical in sorted(mass):
        cumulative += mass[critical]
        if cumulative >= 1 - eta:
            break
    empirical_covariance = sum((e * e.T for e in errors), zeros(dimension)) / len(errors)
    assert empirical_covariance == omega / count
    covered = sum(Q(1, len(errors)) for e in errors
                  if (count * e.T * inverse * e)[0] <= critical)
    assert covered == cumulative and covered >= 1 - eta
    return omega, inverse, critical, covered


def main():
    signs = list(product((-1, 1), repeat=2))
    noise = [Matrix([Q(s, 100), Q(s + t, 100), Q(t, 100)]) for s, t in signs]
    omega, inverse, critical, covered = calibration(noise)
    assert omega == Matrix([[1, 1, 0], [1, 2, 1], [0, 1, 1]]) / 10000
    assert omega.rank() == 2 and omega[1, 2] != 0
    assert critical == 2 and covered == Q(3, 4)
    invisible = Matrix([1, -1, 1]) / 100
    assert (invisible.T * inverse * invisible)[0] == 0  # quadratic alone would accept
    assert omega * inverse * invisible != invisible   # range restriction rejects

    # A literal M4 return family with this noise and a positive-return vertex box.
    loading = Matrix([[1, Q(1, 2)]])
    for theta in (Matrix(t) for t in product((-Q(1, 50), Q(1, 50)), repeat=3)):
        for (s, t), z in zip(signs, noise):
            factors = theta[:2, :] + z[:2, :]
            ra = (loading * factors)[0] + theta[2] + z[2]
            re = factors[0] - Q(s, 200)  # ETF loading (1,0), zero drag
            assert 1 + ra > 0 and 1 + re > 0
            observed = Matrix([factors[0], factors[1], ra - (loading * factors)[0]])
            assert observed == theta + z
    theta = Matrix([Q(1, 100)] * 3)
    histories = list(product(noise, repeat=2))
    hits = 0
    estimates_outside_box = 0
    for h in histories:
        estimate = sum((theta + z for z in h), zeros(3, 1)) / 2
        e = estimate - theta
        if (2 * e.T * inverse * e)[0] <= critical:
            hits += 1
        estimates_outside_box += int(any(abs(x) > Q(1, 50) for x in estimate))
    assert Q(hits, len(histories)) == Q(3, 4)
    assert estimates_outside_box > 0  # estimator is intentionally not projected

    independent = [Matrix(s) / 100 for s in product((-1, 1), repeat=3)]
    full, _, threshold, probability = calibration(independent)
    assert full.rank() == 3 and threshold == 4 and probability == Q(7, 8)
    degenerate, pinv, threshold, probability = calibration([zeros(3, 1)])
    assert degenerate == pinv == zeros(3) and threshold == 0 and probability == 1
    print("M4 definition checks passed: cross-covariance, range restriction, finite quantiles and observables.")
    print("These exact examples do not establish the proposed uniform coverage/certificate theorem.")


if __name__ == "__main__":
    main()
