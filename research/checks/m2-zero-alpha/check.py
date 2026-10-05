"""Four exact M2 limiting-case checks, not a general non-participation theorem.

Run: uv run python checks/m2-zero-alpha/check.py
All parameters are assumed. One active fund and one ETF have B=(1,0), alpha=0,
ETF drag=0, lambda=(1/50,0), gamma=1, zero residuals and two equiprobable
factor shocks (+/-1/10,0). Both instruments have exactly the same returns.
Uses the direct score and exact supporting inequalities; imports no optimizer.
"""

from fractions import Fraction as F


MEAN, VARIANCE = F(1, 50), F(1, 100)
ZERO, ONE, COST = F(0), F(1), F(1, 100)


def score(holding, initial, buy, sell):
    trade = [x - old for x, old in zip(holding, initial)]
    tau = sum(kp * max(v, 0) + km * max(-v, 0)
              for v, kp, km in zip(trade, buy, sell))
    total = sum(holding)
    return MEAN * total - VARIANCE * total**2 / 2 - tau


def certify(name, initial, limits, buy, sell, holding, cost_slope):
    assert all(0 <= x <= cap <= 1 for x, cap in zip(initial, limits))
    assert sum(initial) <= 1
    assert all(0 <= k < 1 for k in buy + sell)
    assert all(0 <= x <= cap for x, cap in zip(holding, limits))
    trades = [x - old for x, old in zip(holding, initial)]
    tau = sum(kp * max(v, 0) + km * max(-v, 0)
              for v, kp, km in zip(trades, buy, sell))
    cash = 1 - sum(holding) - tau
    assert cash >= 0
    for v, t, kp, km in zip(trades, cost_slope, buy, sell):
        assert t == kp if v > 0 else t == -km if v < 0 else -km <= t <= kp
    # ETF is free and held positively in the first, third and fourth cases.
    # The same multiplier works at the zero-ETF boundary in the second case.
    multiplier = MEAN - VARIANCE * sum(holding)
    assert multiplier >= 0 and multiplier * cash == 0
    residuals = [MEAN - VARIANCE * sum(holding) - multiplier - (1 + multiplier) * t
                 for t in cost_slope]
    for w, cap, residual in zip(holding, limits, residuals):
        if cap == 0:
            continue
        assert residual <= 0 if w == 0 else residual >= 0 if w == cap else residual == 0
    # Concavity and these signed residuals certify the candidate globally on the
    # common funded box, including cost kinks. Strict boundary residuals exclude
    # any optimum moving that coordinate away from the chosen bound.
    value = score(holding, initial, buy, sell)
    print(f"{name}: holding={holding}, score={value}, cash={cash}, residual={residuals}")
    return value, residuals


def main():
    assert all(1 + MEAN + shock > 0 for shock in (F(-1, 10), F(1, 10)))
    assert (F(-1, 10)**2 + F(1, 10)**2) / 2 == VARIANCE
    zero_cost = (ZERO, ZERO)
    active_cost = (COST, ZERO)
    cash_start, active_start = (ZERO, ZERO), (ONE, ZERO)
    unit_limits = (ONE, ONE)

    value, residual = certify("no initial active holding; active purchase costs",
                             cash_start, unit_limits, active_cost, active_cost,
                             (ZERO, ONE), (COST, ZERO))
    assert residual[0] < 0  # Every optimizer has a=0 in this case.

    retained, residual = certify("existing active holding; active sale costs",
                                active_start, unit_limits, active_cost, active_cost,
                                (ONE, ZERO), (-COST, ZERO))
    assert residual[0] > 0  # Every optimizer has a=1; funding then forces p=0.
    liquidated = score((ZERO, ONE - COST), active_start, active_cost, active_cost)
    assert retained > liquidated
    print(f"  sale-and-replacement score={liquidated}; loss={retained - liquidated}")

    tied, _ = certify("zero costs; an ETF-only optimum",
                      cash_start, unit_limits, zero_cost, zero_cost,
                      (ZERO, ONE), zero_cost)
    assert score((ONE, ZERO), cash_start, zero_cost, zero_cost) == tied
    print("  all-active holding ties: non-participation is not unique")

    constrained, _ = certify("zero costs; ETF position cap",
                             cash_start, (ONE, F(1, 4)), zero_cost, zero_cost,
                             (F(3, 4), F(1, 4)), zero_cost)
    # For a=0 the score is increasing over 0<=p<=1/4, since its derivative
    # MEAN - VARIANCE*p is positive there; evaluate the ETF-only maximum.
    assert MEAN - VARIANCE * F(1, 4) > 0
    etf_only = score((ZERO, F(1, 4)), cash_start, zero_cost, zero_cost)
    assert constrained > etf_only
    print(f"  ETF-only maximum={etf_only}; full-class gap={constrained - etf_only}")
    print("PASS: four exact M2 cases; no general or empirical conclusion asserted.")


if __name__ == "__main__":
    main()
