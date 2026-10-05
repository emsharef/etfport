"""Exact finite checks for claim 014 (M4), not its all-sample-size proof.

Aggregate full observable histories, independently optimize endpoint testing power,
and exercise the explicit uniform-in-alpha rule and prescribed one-record gate.
Run: uv run python checks/014/check.py
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product

import sympy as sp


H = F(1, 10)
MU = F(1, 80)
BREAK_EVEN = F(13, 1600)
GAP = F(147, 1600)


def atoms(kind, alpha):
    """Full observation (f1, f2, rA, rE); no hidden signs reach a rule."""
    out = defaultdict(F)
    for s, t, u in product((-1, 1), repeat=3):
        ze = F(t * (3 - (u if kind == 'I' else s)), 20)
        out[(MU, F(0), alpha + H * s, MU + ze)] += F(1, 8)
    assert sum(out.values()) == 1
    return dict(out)


def histories(kind, alpha, count):
    law = {(): F(1)}
    for _ in range(count):
        next_law = defaultdict(F)
        for hist, mass in law.items():
            for obs, probability in atoms(kind, alpha).items():
                next_law[hist + (obs,)] += mass * probability
        law = dict(next_law)
    assert sum(law.values()) == 1
    return law


def optimal_test_power(null, alternative, eta):
    """Exact finite one-budget linear optimization, independent of the witness rule.

    Null-free atoms cost nothing. For the remaining atoms allocate rejection
    probability in decreasing alternative/null ratio, splitting the last atom.
    Swapping budget from a smaller to a larger ratio cannot reduce power.
    """
    power = sum(p for obs, p in alternative.items() if null.get(obs, 0) == 0)
    budget = eta
    ranked = sorted(((p / null[obs], null[obs], p)
                     for obs, p in alternative.items() if null.get(obs, 0) > 0),
                    reverse=True)
    for _, cost, benefit in ranked:
        probability = min(F(1), budget / cost)
        power += probability * benefit
        budget -= probability * cost
    return power


def witness_probability(kind, hist, eta):
    """Conditional chance to certify w_A; uses only public observations."""
    if kind == 'R':
        inferred = []
        for _, _, ra, re in hist:
            magnitude = abs(re - MU)
            if magnitude not in (H, 2 * H):
                return F(0)
            inferred.append(ra - (H if magnitude == H else -H))
    else:
        inferred = [ra - (H if ra > 0 else -H)
                    for _, _, ra, _ in hist if ra != 0]
        if not inferred:
            return min(F(1), eta * 2 ** len(hist))
    if len(set(inferred)) != 1 or not -H <= inferred[0] <= H:
        return F(0)
    return F(inferred[0] > BREAK_EVEN)


def check_moments_and_economics():
    covariances = []
    marginal_laws = []
    for kind in ('I', 'R'):
        law = atoms(kind, F(0))
        means = [sum(mass * obs[i] for obs, mass in law.items()) for i in range(4)]
        assert means == [MU, 0, 0, MU]
        covariance = [[sum(mass * (obs[i] - means[i]) * (obs[j] - means[j])
                           for obs, mass in law.items()) for j in range(4)]
                      for i in range(4)]
        assert covariance == [[0, 0, 0, 0], [0, 0, 0, 0],
                              [0, 0, F(1, 100), 0], [0, 0, 0, F(1, 40)]]
        covariances.append(covariance)
        marginals = []
        for i in range(4):
            marginal = defaultdict(F)
            for obs, mass in law.items():
                marginal[obs[i]] += mass
            marginals.append(dict(marginal))
        marginal_laws.append(marginals)
        for alpha in (-H, H):
            for obs in atoms(kind, alpha):
                assert 1 + obs[2] > 0 and 1 + obs[3] > 0
    assert covariances[0] == covariances[1]
    assert marginal_laws[0] == marginal_laws[1]

    a, p, alpha = sp.symbols('a p alpha', real=True)
    q = a * alpha + p / 80 - a**2 / 200 - p**2 / 80
    assert sp.expand(q.subs(a, 0) - (1 - (2*p - 1)**2) / 320) == 0
    assert sp.expand(q.subs({a: 1, p: 0}) - sp.Rational(1, 320)
                     - (alpha - sp.Rational(13, 1600))) == 0
    gap_from_full = q.subs({a: 1, p: 0, alpha: sp.Rational(1, 10)}) - q.subs(alpha, sp.Rational(1, 10))
    # Nonnegative remainder in the claimed full-optimum lower bound, for a+p<=1.
    remainder = (1-a)**2 / 200 + (1-a-p) / 80 + p**2 / 80
    assert sp.expand(gap_from_full - sp.Rational(31, 400)*(1-a) - remainder) == 0
    assert H - BREAK_EVEN == GAP


def score(w, alpha):
    a, p = w
    return a * alpha + p / 80 - a*a / 200 - p*p / 80


def exact_candidate(alpha_hat):
    """Optimize the quadratic independently over every face of the funded triangle.

    Strict concavity ensures a maximum is either the unconstrained stationary
    point or an edge maximum. Each edge is a univariate concave quadratic.
    """
    clip = lambda a: max(F(0), min(F(1), a))
    budget_a = clip((alpha_hat + MU) / F(7, 200))
    candidates = {(F(0), F(1, 2)), (clip(100 * alpha_hat), F(0)),
                  (budget_a, 1-budget_a)}
    interior = (100 * alpha_hat, F(1, 2))
    if interior[0] >= 0 and sum(interior) <= 1:
        candidates.add(interior)
    best = max(score(w, alpha_hat) for w in candidates)
    return min(w for w in candidates if score(w, alpha_hat) == best)


def gate_diagnostics(kind, alpha, count, eta):
    """Exact quantile, confidence interval, plug-in optimization and infimum."""
    errors = defaultdict(F)
    for signs in product((-1, 1), repeat=count):
        errors[H * sum(signs) / count] += F(1, 2**count)
    statistics = defaultdict(F)
    for error, mass in errors.items():
        statistics[count * error**2 / H**2] += mass
    cumulative = F(0)
    for critical in sorted(statistics):
        cumulative += statistics[critical]
        if cumulative >= 1-eta:
            break
    radius = max(abs(e) for e in errors if count * e**2 / H**2 <= critical)
    assert count * radius**2 / H**2 == critical
    power = coverage = empty = F(0)
    rows = {}
    for hist, mass in histories(kind, alpha, count).items():
        estimate = sum(obs[2] for obs in hist) / count
        lo, hi = max(-H, estimate-radius), min(H, estimate+radius)
        candidate = exact_candidate(estimate)
        assert min(candidate) >= 0 and sum(candidate) <= 1
        covered = lo <= alpha <= hi
        is_empty = lo > hi
        # Adv is increasing in alpha for fixed funded a>=0; E optimum is constant.
        lower = None if is_empty else score(candidate, lo) - F(1, 320)
        certify = not is_empty and candidate[0] > 0 and lower > 0
        coverage += mass * covered
        empty += mass * is_empty
        power += mass * certify
        rows[estimate] = (lo, hi, candidate, lower, certify)
    return critical, radius, power, coverage, empty, rows


def check_gate_loss_attribution():
    eta = F(1, 4)
    expected = {
        1: (F(1), H, F(1, 2), F(1), F(0)),
        2: (F(2), H, F(1, 4), F(1), F(0)),
        3: (F(1, 3), H/3, F(3, 4), F(3, 4), F(1, 8)),
    }
    for count, target in expected.items():
        first = gate_diagnostics('I', H, count, eta)
        second = gate_diagnostics('R', H, count, eta)
        assert first == second and first[:5] == target
        if count == 3:
            assert first[5][2*H][0] > first[5][2*H][1]  # all-positive history: empty set
    null, alternative = histories('I', -H, 1), histories('I', H, 1)
    assert optimal_test_power(null, alternative, F(0)) == F(1, 2)
    assert optimal_test_power(null, alternative, eta) == F(3, 4)
    off_overlap = on_overlap = F(0)
    for hist, mass in alternative.items():
        if hist[0][2] != 0:
            assert gate_diagnostics('I', H, 1, eta)[5][hist[0][2]][4]
            assert witness_probability('I', hist, eta) == 1
            off_overlap += mass
        else:
            on_overlap += mass * witness_probability('I', hist, eta)
    false_at_null = sum(m * witness_probability('I', hist, eta) for hist, m in null.items())
    assert off_overlap == F(1, 2) and on_overlap == false_at_null == eta
    print('Gate diagnostics at eta=1/4, theta_+: N_obs=1,2,3 powers are 1/2,1/4,3/4.')
    print('One-record I benchmark gain 1/4 is entirely certification on shared zero-return histories,')
    print('with false certification 1/4 at theta_-; every nonzero positive-endpoint record is already certified.')


def main():
    check_moments_and_economics()
    check_gate_loss_attribution()
    alphas = (-H, -H/2, F(0), BREAK_EVEN, F(1, 40), H)
    for count in (1, 2, 3):
        for kind in ('I', 'R'):
            null, alternative = histories(kind, -H, count), histories(kind, H, count)
            overlap = sum(min(null.get(x, 0), p) for x, p in alternative.items())
            assert overlap == (F(1, 2**count) if kind == 'I' else 0)
            if kind == 'I':
                common = set(null) & set(alternative)
                assert all(all(obs[2] == 0 for obs in hist) for hist in common)
                assert all(null[hist] == alternative[hist] for hist in common)
            for eta in (F(1, 16), F(1, 4), F(3, 4)):
                optimum = optimal_test_power(null, alternative, eta)
                target = min(F(1), 1 - F(1, 2**count) + eta) if kind == 'I' else F(1)
                assert optimum == target
                attained = sum(mass * witness_probability(kind, hist, eta)
                               for hist, mass in alternative.items())
                assert attained == optimum
                for alpha in alphas:
                    law = histories(kind, alpha, count)
                    false = sum(mass * witness_probability(kind, hist, eta)
                                for hist, mass in law.items() if alpha <= BREAK_EVEN)
                    assert false <= eta
                    # The estimate's law must not inherit the ETF signal distinction.
                    estimates = defaultdict(F)
                    for hist, mass in law.items():
                        estimates[sum(obs[2] for obs in hist) / count] += mass
                    other = defaultdict(F)
                    for hist, mass in histories('R' if kind == 'I' else 'I', alpha, count).items():
                        other[sum(obs[2] for obs in hist) / count] += mass
                    assert estimates == other

    # One-record M4 calibration: a single atom of T=1 at either shock sign.
    for noise in (-H, H):
        assert noise**2 / F(1, 100) == 1
    for kind in ('I', 'R'):
        power = F(0)
        for obs, mass in atoms(kind, H).items():
            estimate = obs[2]
            interval = (max(-H, estimate-H), min(H, estimate+H))
            if estimate == 0:
                assert interval == (-H, H)   # null forbids every active certificate
            else:
                assert estimate == 2*H and interval == (H, H)
                assert H - BREAK_EVEN == GAP > 0
                power += mass
        assert power == F(1, 2)
    print('Claim 014 exact checks passed: equal moments and economics; full-history bounds; M4 gate.')
    print('N_obs=1, eta=1/4: full-history power I=3/4, R=1; prescribed M4 gate=1/2 in both.')
    print('Finite checks only; the claim contains the all-N_obs, all-eta, all-alpha paper proof.')


if __name__ == '__main__':
    main()
