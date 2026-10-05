"""Exact checks of M3 cash-composition funding; no optimizer or experiment.

Run: uv run python checks/m3-cash-composition/check.py
"""
from fractions import Fraction as F


def cost(order, buy, sell):
    return buy * max(order, 0) + sell * max(-order, 0)


def cash_after(cash, active_target, etf_target, etf_buy, etf_sell):
    # Original funding equation, with fixed W=1 and active incumbent 1/4.
    active_before = F(1, 4)
    etf_before = 1 - active_before - cash
    ua, ue = active_target - active_before, etf_target - etf_before
    return cash - ua - ue - cost(ua, F(1, 100), F(1, 10)) - cost(ue, etf_buy, etf_sell)


def main():
    old, new = F(1, 4), F(1, 2)
    delta = new - old
    buy, sell = F(1, 50), F(3, 100)
    # Same-side sale, same-side buy, and two opposite-sign crossing cases.
    cases = ((F(1, 10), F(3, 400)), (F(3, 5), -F(1, 200)),
             (F(7, 20), F(1, 400)), (F(9, 20), -F(1, 400)),
             (F(1, 4), F(3, 400)), (F(1, 2), -F(1, 200)))
    for p, expected in cases:
        before = cash_after(old, F(1, 5), p, buy, sell)
        after = cash_after(new, F(1, 5), p, buy, sell)
        assert before >= 0 and after >= 0
        assert after - before == expected
        assert -buy * delta <= after - before <= sell * delta
        v = p - F(1, 2)
        assert after - before == cost(v, buy, sell) - cost(v + delta, buy, sell)
    # The two root classes include active buys, sales, and unchanged active units.
    # Infeasible targets must remain infeasible too, not merely feasible examples.
    targets = ((F(3, 10), F(2, 5)), (F(1, 4), F(1, 2)),
               (F(0), F(19, 20)), (F(4, 5), F(2, 5)))
    saw_feasible, saw_infeasible = False, False
    for a, p in targets:
        cashes = [cash_after(c, a, p, F(0), F(0))
                  for c in (F(0), old, new, F(3, 4))]
        assert len(set(cashes)) == 1
        saw_feasible |= cashes[0] >= 0
        saw_infeasible |= cashes[0] < 0
        # Equal post-root states mark identically on every tested observation.
        for da, de in ((F(3, 2), F(1, 2)), (F(97, 100), F(103, 100))):
            marked = [(a * da, p * de, h) for h in cashes]
            assert len(set(marked)) == 1
    assert saw_feasible and saw_infeasible
    print("M3 cash-composition checks passed: cost signs, kinks, and free-ETF target invariance.")


if __name__ == "__main__":
    main()
