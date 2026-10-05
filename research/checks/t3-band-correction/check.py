"""Independent exact M2 check of the candidate alpha-band formula.

All inputs assumed; no experiment solver imported. One active fund and one ETF,
both B=(1,0), zero ETF drag, gamma=1, a^-=p^-=1/2 and cash zero. Active buy/sell
costs are 1/100; ETF costs zero. Independent symmetric factor, active-residual,
ETF-residual shocks have sizes 1/10, 1/50, 1/100. Initial limits are both one.
Run: uv run python checks/t3-band-correction/check.py
"""

from fractions import Fraction as F
from itertools import product


COST = F(1, 100)
START = (F(1, 2), F(1, 2))
SHOCKS = [(s * F(1, 10) + a * F(1, 50), s * F(1, 10) + e * F(1, 100))
          for s, a, e in product((-1, 1), repeat=3)]
SIGMA = [[sum(x[i] * x[j] for x in SHOCKS) / len(SHOCKS) for j in range(2)]
         for i in range(2)]


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def score(w, alpha, premium):
    return ((premium + alpha) * w[0] + premium * w[1]
            - dot(w, [dot(row, w) for row in SIGMA]) / 2
            - COST * abs(w[0] - START[0]))


def holding(trade):
    return (START[0] + trade, START[1] - trade - COST * abs(trade))


def polynomial(alpha, premium, sign):
    """Independently recover exact constant/linear/quadratic coefficients."""
    step = F(sign, 8)
    q0 = score(holding(F(0)), alpha, premium)
    q1 = score(holding(step), alpha, premium)
    q2 = score(holding(2 * step), alpha, premium)
    quadratic = (q2 - 2 * q1 + q0) / (2 * step**2)
    linear = (q1 - q0 - quadratic * step**2) / step
    assert quadratic < 0
    return q0, linear, quadratic


def check(premium, check_full_optimizer):
    multiplier = premium - dot(SIGMA[1], START)
    smooth_active = premium - dot(SIGMA[0], START)
    assert multiplier >= 0
    # In E, p<=1/2; its smooth derivative decreases to multiplier at p=1/2.
    # Thus p=1/2 is the unique ETF-only optimum and its interior-coordinate
    # stationarity pins the cash multiplier to the displayed value.
    assert SIGMA[1][1] > 0
    _, left_slope, _ = polynomial(F(0), premium, -1)
    _, right_slope, _ = polynomial(F(0), premium, 1)
    lower, upper = -left_slope, -right_slope
    assert lower == multiplier - (1 + multiplier) * COST - smooth_active
    assert upper == multiplier + (1 + multiplier) * COST - smooth_active
    width = upper - lower
    corrected = 2 * COST * (1 + multiplier)
    wrong = COST * (1 + multiplier) + COST * (1 - multiplier)
    assert width == corrected
    assert (width != wrong) == (multiplier > 0)

    epsilon = F(1, 10**6)
    for alpha, expected in ((lower - epsilon, -1), (lower, 0),
                            ((lower + upper) / 2, 0), (upper, 0), (upper + epsilon, 1)):
        assert all(1 + premium + alpha + x[0] > 0 and 1 + premium + x[1] > 0 for x in SHOCKS)
        if expected == 0:
            # Full-domain concavity certificate at w^-: ETF residual zero and
            # active cost subgradient in [-COST,COST], with complementary cash.
            active_slope = (smooth_active + alpha - multiplier) / (1 + multiplier)
            assert -COST <= active_slope <= COST
        if check_full_optimizer:
            # premium=1/50 makes the ETF marginal positive everywhere funded:
            # p+a<=1 gives premium - Sigma_EA*a - Sigma_EE*p >= premium-max(row)>0.
            assert premium > max(SIGMA[1])
            # Hence cash binds at the full optimum. Maximize each exact concave
            # quadratic on its trade interval, then compare with the kink.
            candidates = [F(0)]
            for sign, lo, hi in ((-1, -START[0], F(0)),
                                 (1, F(0), START[1] / (1 + COST))):
                _, linear, quadratic = polynomial(alpha, premium, sign)
                candidates.append(min(hi, max(lo, -linear / (2 * quadratic))))
            best = max(candidates, key=lambda v: score(holding(v), alpha, premium))
            assert (best > 0) - (best < 0) == expected
            w = holding(best)
            assert all(0 <= x <= 1 for x in w)
            assert 1 - sum(w) - COST * abs(best) == 0
        elif expected:
            # Outside either endpoint the indicated funded direction has positive
            # first-order gain. Verify a sufficiently small exact move improves.
            _, linear, quadratic = polynomial(alpha, premium, expected)
            step = F(expected) * min(F(1, 100), abs(linear / (2 * quadratic)))
            assert score(holding(step), alpha, premium) > score(START, alpha, premium)
    print(f"premium={premium}: cash=0, multiplier={multiplier}, band=[{lower}, {upper}], width={width}")
    print(f"  candidate's printed width={wrong}; corrected width={corrected}")


if __name__ == "__main__":
    assert SIGMA[0][0] * SIGMA[1][1] - SIGMA[0][1]**2 > 0
    check(F(1, 50), True)
    check(dot(SIGMA[1], START), False)
    print("PASS: sale-cost sign corrected; tight budget can have zero multiplier and costs-only width.")
