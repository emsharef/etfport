"""Exact finite checks for claim 008; not a proof or an empirical experiment.

Run: uv run python checks/008/check.py
Construct returns and wealth directly; do not import a solver or the claim's
score formula. All cases and rational holdings below are fixed assumed inputs.
"""
from fractions import Fraction as F
from itertools import product

ZERO, ONE = F(0), F(1)
SCENARIOS = tuple(product((-1, 1), repeat=2))
Q = F(1, 4)
GRID = tuple(F(i, 4) for i in range(5))


def moments(values):
    mean = sum(Q * x for x in values)
    return mean, sum(Q * (x - mean) ** 2 for x in values)


def cost(w, initial, buy, sell):
    trade = w[0] - initial[0]
    return buy * max(trade, ZERO) + sell * max(-trade, ZERO)


def cash(w, initial, buy, sell):
    return ONE - sum(w) - cost(w, initial, buy, sell)


def returns(lam, alpha, epsilon):
    etf = [lam + F(s, 10) for s, _ in SCENARIOS]
    active = [r + alpha + e for r, e in zip(etf, epsilon)]
    assert all(ONE + r > 0 for r in active + etf)
    return active, etf


def wealth(w, initial, buy, sell, active, etf):
    k = cash(w, initial, buy, sell)
    return [k + w[0] * (ONE + r_a) + w[1] * (ONE + r_e)
            for r_a, r_e in zip(active, etf)]


def score(w, initial, buy, sell, gamma, support, epsilon):
    result = ZERO
    for mass, lam, alpha in support:
        active, etf = returns(lam, alpha, epsilon)
        terminal = wealth(w, initial, buy, sell, active, etf)
        mean, variance = moments([value - ONE for value in terminal])
        result += mass * (mean - gamma * variance / 2)
    return result


def check_case(name, initial, buy, sell, gamma, support, epsilon):
    assert initial[0] == 0 or sell == 0
    assert all(0 <= x <= 1 for x in initial) and sum(initial) <= 1
    assert 0 <= buy < 1 and 0 <= sell < 1 and gamma >= 0
    assert sum(m for m, _, _ in support) == 1
    assert sum(m * alpha for m, _, alpha in support) == 0
    xi = [F(s, 10) for s, _ in SCENARIOS]
    assert moments(epsilon)[0] == 0
    assert sum(Q * x * e for x, e in zip(xi, epsilon)) == 0
    residual_variance = moments(epsilon)[1]
    seen = False
    for w in product(GRID, repeat=2):
        if cash(w, initial, buy, sell) < 0:
            continue
        seen = True
        replacement = (ZERO, sum(w))
        tau = cost(w, initial, buy, sell)
        assert 0 <= replacement[1] <= 1
        assert cost(replacement, initial, buy, sell) == 0
        assert cash(replacement, initial, buy, sell) >= 0
        assert cash(replacement, initial, buy, sell) - cash(w, initial, buy, sell) == tau
        improvement = (score(replacement, initial, buy, sell, gamma, support, epsilon)
                       - score(w, initial, buy, sell, gamma, support, epsilon))
        assert improvement == tau + gamma * w[0] ** 2 * residual_variance / 2
        assert improvement >= 0
        if w[0] > 0 and (gamma * residual_variance > 0 or (initial[0] == 0 and buy > 0)):
            assert improvement > 0
        if all(alpha == 0 for _, _, alpha in support) and all(e == 0 for e in epsilon):
            for _, lam, alpha in support:
                active, etf = returns(lam, alpha, epsilon)
                assert active == etf
                original = wealth(w, initial, buy, sell, active, etf)
                replaced = wealth(replacement, initial, buy, sell, active, etf)
                assert all(v - u == tau for u, v in zip(original, replaced))
    assert seen
    print(f"PASS: {name}")


def main():
    known = ((ONE, F(1, 50), ZERO),)
    uncertain = ((F(1, 2), F(1, 100), F(-1, 100)),
                 (F(1, 2), F(3, 100), F(1, 100)))
    residual = tuple(F(3 * s, 100) for _, s in SCENARIOS)
    exact = (ZERO,) * 4
    check_case("no incumbent, positive residual risk, mean-zero-alpha belief",
               (ZERO, F(1, 4)), F(1, 100), F(1, 50), ONE, uncertain, residual)
    check_case("free active sale with incumbent and residual risk",
               (F(1, 2), F(1, 4)), F(1, 100), ZERO, ONE, known, residual)
    check_case("exact returns, positive purchase cost",
               (ZERO, F(1, 4)), F(1, 100), F(1, 50), ONE, known, exact)
    check_case("free incumbent liquidation under exact returns",
               (F(1, 2), F(1, 4)), F(1, 100), ZERO, ONE, known, exact)
    check_case("zero risk coefficient and free trading give weak dominance",
               (ZERO, ZERO), ZERO, ZERO, ZERO, uncertain, residual)

    # Removing the cross-moment restriction can reverse the inequality.
    negative_covariance = tuple(F(-s, 20) for s, _ in SCENARIOS)
    assert sum(Q * F(s, 10) * e for (s, _), e in zip(SCENARIOS, negative_covariance)) < 0
    w, replacement, initial = (F(1, 2), ZERO), (ZERO, F(1, 2)), (ZERO, ZERO)
    improvement = (score(replacement, initial, ZERO, ZERO, ONE, known, negative_covariance)
                   - score(w, initial, ZERO, ZERO, ONE, known, negative_covariance))
    assert improvement < 0
    print("PASS: negative cross-moment invalidates weak replacement dominance")


if __name__ == "__main__":
    main()
