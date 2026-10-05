"""Independent exact check of experiment 005's T1 equal-cost example (M2).

Run with uv run python checks/exp005-equal-cost/check.py.
Does not import the experiment solver. Inputs are assumed, not observed.
Checks full and ETF-only funded optimizers, their score gap and exposure matching.
"""

from fractions import Fraction as F
from itertools import product


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def check(n, action_class="F"):
    assert action_class in ("F", "E")
    cost = F(1, 2000)
    loadings = [(F(1), F(1, 2)), (F(1), F(0)), (F(1), F(1, 4))][:n + 1]
    residual = [F(3, 100), F(1, 200), F(1, 100)][:n + 1]
    initial = [F(1, 2), F(1, 3), F(0)][:n + 1]
    means = [F(1, 50), F(201, 10000), F(17, 800)][:n + 1]
    # Construct all independent symmetric shocks and compute covariance directly.
    shocks = []
    for signs in product((-1, 1), repeat=n + 3):
        factor = (signs[0] * F(3, 50), signs[1] * F(1, 50))
        shocks.append([dot(b, factor) + signs[i + 2] * residual[i]
                       for i, b in enumerate(loadings)])
    for i, mean in enumerate(means):
        assert sum(s[i] for s in shocks) == 0
        assert all(1 + mean + s[i] > 0 for s in shocks)
    covariance = [[sum(s[i] * s[j] for s in shocks) / len(shocks)
                   for j in range(n + 1)] for i in range(n + 1)]
    # Candidate holdings follow directly from exhausting cash after the proposed
    # active/ETF sales. No optimizer values from the experiment are used.
    if n == 1:
        holding = [initial[0], initial[1] + F(1, 6) / (1 + cost)]
    elif action_class == "F":
        holding = [F(0), F(0), (1 - cost * sum(initial)) / (1 + cost)]
    else:
        holding = [initial[0], F(0), (F(1, 6) + (1 - cost) * initial[1]) / (1 + cost)]
    if action_class == "E":
        assert holding[0] == initial[0]
    trade = [x - old for x, old in zip(holding, initial)]
    tau = cost * sum(abs(v) for v in trade)
    assert 1 - sum(holding) - tau == 0
    assert all(0 <= w <= 1 for w in holding)
    gradient = [mu - dot(row, holding) for mu, row in zip(means, covariance)]
    multiplier = (gradient[-1] - cost) / (1 + cost)
    assert multiplier > 0
    subgradient = []
    for i, v in enumerate(trade):
        t = (F(0) if action_class == "E" and i == 0 else
             cost if v > 0 else -cost if v < 0
             else (gradient[i] - multiplier) / (1 + multiplier))
        assert -cost <= t <= cost
        subgradient.append(t)
    # For any feasible z, concavity and the cost subgradient bound the score
    # change above by this residual dotted with z-holding, plus multiplier times
    # the nonpositive change in the binding cash outlay. Check the signs exactly.
    residual_gradient = [g - multiplier - (1 + multiplier) * t
                         for g, t in zip(gradient, subgradient)]
    for i, (w, r) in enumerate(zip(holding, residual_gradient)):
        if action_class == "E" and i == 0:
            continue  # Equality constraint: every comparison has zero active change.
        assert r <= 0 if w == 0 else r >= 0 if w == 1 else r == 0
    # Positive residual variances give strict concavity (gamma=1): the covariance
    # quadratic is a sum of factor squares plus sum_i residual[i]^2 * d_i^2.
    assert all(s > 0 for s in residual)
    value = dot(means, holding) - dot(holding, [dot(row, holding) for row in covariance]) / 2 - tau
    no_trade_value = dot(means, initial) - dot(initial, [dot(row, initial) for row in covariance]) / 2
    assert value > no_trade_value
    print(f"n={n}, {action_class}: holding={tuple(holding)}, trade={tuple(trade)}, cash=0, score={value}")
    print(f"  exact cash multiplier={multiplier}; stationarity residual={residual_gradient}")
    return holding, trade, value


def main():
    one, trade_one, full_one = check(1)
    two, trade_two, full_two = check(2)
    etf_one, _, value_etf_one = check(1, "E")
    etf_two, _, value_etf_two = check(2, "E")
    assert trade_one[0] == 0 and trade_one[1] > 0
    assert trade_two[0] == -F(1, 2)
    assert one[0] == F(1, 2) and two[0] == 0
    assert one == etf_one and full_one == value_etf_one
    assert full_two > value_etf_two
    print(f"full minus ETF-only score: n=1: {full_one - value_etf_one}; n=2: {full_two - value_etf_two}")
    # E1=(1,0), E2=(1,1/4) have independent loadings. Solve the two
    # exposure equations directly, retaining the required active holding 1/2.
    target = (sum(two), two[0] / 2 + two[2] / 4)
    matching_p2 = 4 * (target[1] - F(1, 4))
    matching_p1 = target[0] - F(1, 2) - matching_p2
    assert F(1, 2) + matching_p1 + matching_p2 == target[0]
    assert F(1, 4) + matching_p2 / 4 == target[1]
    assert matching_p2 < 0
    print(f"ETF-only holdings needed to match full optimum: p=({matching_p1}, {matching_p2}); shorting required")
    print("PASS: funded class gap and constrained exposure matching checked exactly for this assumed instance.")


if __name__ == "__main__":
    main()
