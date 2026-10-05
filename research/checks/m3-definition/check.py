"""Assumed M3 definition checks, not optimization or a performance experiment.

Run: uv run python checks/m3-definition/check.py
Exact finite Bayes and wealth arithmetic; floating exponential utility is used
only to check the two equivalent sums for each fixed feasible policy.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import exp, isclose, log

W0 = F(1)
RHO = F(1)
THETA = tuple((lam, F(1, 100), alpha)
              for lam, alpha in product((F(0), F(1, 50)), repeat=2))
PI = {theta: F(1, 4) for theta in THETA}
SIGNS = tuple(product((-1, 1), repeat=4))
Q = F(1, 16)
BUY = (F(1, 1000), F(3, 2000))
SELL = (F(1, 500), F(1, 2000))
DRAG = F(-1, 10000)
INITIAL = ((F(1, 4), F(1, 4)), F(1, 2))


def observation(theta, signs):
    lam1, lam2, alpha = theta
    sf1, sf2, sa, se = signs
    factors = (lam1+F(sf1, 100), lam2+F(sf2, 200))
    active = factors[0]+factors[1]/2+alpha+F(sa, 100)
    etf = factors[0]-DRAG+F(se, 200)
    assert 1+active > 0 and 1+etf > 0
    return factors, (active, etf)


def review(state, trade):
    x, h = state
    cost = sum(kp*max(u, 0)+km*max(-u, 0) for u, kp, km in zip(trade, BUY, SELL))
    held = tuple(old+u for old, u in zip(x, trade))
    cash = h-sum(trade)-cost
    assert all(z >= 0 for z in held) and cash >= 0
    assert sum(held)+cash+cost == sum(x)+h
    return held, cash


def mark(state, y):
    held, cash = state
    returns = y[1]
    result = tuple(x*(1+r) for x, r in zip(held, returns)), cash
    assert sum(result[0])+result[1] > 0
    return result


def terminal(state, theta, signs):
    held, cash = mark(state, observation(theta, signs))
    return sum(held)+cash


def next_trade(state, arm):
    # Depends only on marked holdings; never on the hidden parameter or next draw.
    if arm == 'F':
        return (-state[0][0]/4, state[0][0]/8)
    if arm == 'E':
        return (F(0), state[1]/(2*(1+BUY[1])))
    assert arm == 'N'
    return (F(0), F(0))


def main():
    assert sum(PI.values()) == 1 and len(SIGNS)*Q == 1
    assert all(0 <= k < 1 for k in BUY+SELL)
    # Every primitive shock is centered, with nonzero variance.
    for i, size in enumerate((F(1, 100), F(1, 200), F(1, 100), F(1, 200))):
        assert sum(Q*signs[i]*size for signs in SIGNS) == 0
        assert sum(Q*(signs[i]*size)**2 for signs in SIGNS) > 0
    likelihood = {theta: defaultdict(F) for theta in THETA}
    for theta, signs in product(THETA, SIGNS):
        likelihood[theta][observation(theta, signs)] += Q
    observations = set().union(*(set(v) for v in likelihood.values()))
    probs = {y: sum(PI[t]*likelihood[t][y] for t in THETA) for y in observations}
    assert sum(probs.values()) == 1 and all(p > 0 for p in probs.values())
    posterior = {y: {t: PI[t]*likelihood[t][y]/probs[y] for t in THETA}
                 for y in observations}
    assert all(sum(post.values()) == 1 for post in posterior.values())
    assert all(sum(probs[y]*posterior[y][t] for y in observations) == PI[t] for t in THETA)
    assert any(all(posterior[y][t] > 0 for t in THETA) for y in observations)
    assert any(any(posterior[y][t] != PI[t] for t in THETA) for y in observations)

    utility_values = []
    for root_trade in ((F(0), F(0)), (F(0), F(1, 20)), (F(-1, 20), F(1, 20))):
        post0 = review(INITIAL, root_trade)
        for arm in ('N', 'E', 'F'):
            # Construct one action per public observation before summing hidden paths.
            post1 = {}
            for y in observations:
                pre1 = mark(post0, y)
                trade1 = next_trade(pre1, arm)
                post1[y] = review(pre1, trade1)
                if arm == 'E':
                    assert post1[y][0][0] == pre1[0][0]
                if arm == 'N':
                    assert post1[y] == pre1
            direct_mean, grouped_mean = F(0), F(0)
            direct_utility, grouped_utility, shifted_utility = 0.0, 0.0, 0.0
            shift = F(1, 7)  # artificial sure terminal payoff in units of W0
            for t, s0, s1 in product(THETA, SIGNS, SIGNS):
                y = observation(t, s0)
                wealth = terminal(post1[y], t, s1)
                pre1 = mark(post0, y)
                wealth1 = sum(pre1[0])+pre1[1]
                rho1 = RHO*wealth1/W0
                assert rho1*wealth/wealth1 == RHO*wealth/W0
                mass = PI[t]*Q*Q
                direct_mean += mass*wealth
                direct_utility += float(mass)*(-exp(-float(RHO*wealth/W0)))
                shifted_utility += float(mass)*(-exp(-float(RHO*(wealth/W0+shift))))
            for y, t, s1 in product(observations, THETA, SIGNS):
                wealth = terminal(post1[y], t, s1)
                mass = probs[y]*posterior[y][t]*Q
                grouped_mean += mass*wealth
                grouped_utility += float(mass)*(-exp(-float(RHO*wealth/W0)))
            assert direct_mean == grouped_mean
            assert isclose(direct_utility, grouped_utility, rel_tol=0, abs_tol=1e-12)
            assert -1 < direct_utility < 0
            ce = -log(-direct_utility)/float(RHO)
            shifted_ce = -log(-shifted_utility)/float(RHO)
            assert isclose(shifted_ce-ce, float(shift), rel_tol=0, abs_tol=1e-12)
            assert isclose(shifted_utility, exp(-float(RHO*shift))*direct_utility,
                           rel_tol=1e-12, abs_tol=0)
            utility_values.append((direct_utility, shifted_utility, ce, shifted_ce))
    # Fixed-policy comparisons only: these values are not class optima.
    for first, second in product(utility_values, repeat=2):
        gap = first[2]-second[2]
        ratio_gap = -log(first[0]/second[0])/float(RHO)
        shifted_gap = first[3]-second[3]
        assert isclose(gap, ratio_gap, rel_tol=0, abs_tol=1e-12)
        assert isclose(gap, shifted_gap, rel_tol=0, abs_tol=1e-12)
    print('PASS: certainty-equivalent ratio and common terminal-shift invariance')
    print('PASS: centered nonzero shocks, positive gross returns, nontrivial public updating')
    print('PASS: overlapping hidden states, one policy action per observation, exact funded wealth')
    print('PASS: N/E/F fixed-policy sums agree and review-1 utility rescaling is exact')
    print('No optimum, gap sign, boundary shift or general theorem asserted')


if __name__ == '__main__':
    main()
