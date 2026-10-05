"""Exact finite checks of claim 006's assumed M2 example; not a general proof.
Run: uv run python checks/006/check.py
"""

from fractions import Fraction as F


PARAMETERS = ((F(1, 100), F(0)), (F(3, 100), F(1, 50)))
SHOCKS = (F(-1, 10), F(1, 10))
MAX_TOTAL = F(100, 101)


def moments(a, p, premium, alpha):
    cost = (a + p) / 100
    cash = 1 - a - p - cost
    assert a >= 0 and p >= 0 and a <= 1 and p <= 1 and cash >= 0
    gains = []
    for shock in SHOCKS:
        gross_a = 1 + premium + alpha + shock
        gross_e = 1 + premium + shock
        assert gross_a > 0 and gross_e > 0
        gains.append(cash + a * gross_a + p * gross_e - 1)
    mean = sum(gains) / 2
    variance = sum((g - mean)**2 for g in gains) / 2
    return mean, variance


def score(a, p):
    return sum(mean - variance / 2 for mean, variance in
               (moments(a, p, premium, alpha) for premium, alpha in PARAMETERS)) / 2


def main():
    for total in (F(0), F(1, 4), F(1, 2), MAX_TOTAL):
        for active in (F(0), total / 2, total):
            passive = total - active
            for premium, alpha in PARAMETERS:
                mean, variance = moments(active, passive, premium, alpha)
                matched_mean, matched_variance = moments(F(0), total, premium, alpha)
                assert variance == matched_variance == total**2 / 100
                assert mean - matched_mean == active * alpha
            assert score(active, passive) == total / 100 + active / 100 - total**2 / 200
            assert score(active, passive) - score(F(0), total) == active / 100
    assert score(F(0), F(0)) == 0
    assert score(F(0), MAX_TOTAL) == F(51, 10201)
    assert score(MAX_TOTAL, F(0)) == F(152, 10201)
    assert score(MAX_TOTAL, F(0)) - score(F(0), MAX_TOTAL) == F(1, 101)
    assert 1 - MAX_TOTAL - MAX_TOTAL / 100 == 0
    print("PASS: claim 006 finite scenario, matched-score and endpoint checks (exact rationals).")


if __name__ == "__main__":
    main()
