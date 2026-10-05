"""Exact finite checks for claim 016, not its arbitrary-law rate proof.

Run: uv run python checks/016/check.py
No fitted data, simulation, or claim about the optimal gate's power is used.
"""
from collections import defaultdict
from itertools import product

import sympy as sp

R = sp.Rational
S = R(1, 1000)
D = (sp.Matrix([1, 0, 1]), sp.Matrix([1, -1, 1]))
C = (sp.Matrix([0, -R(1, 4), 0]), sp.Matrix([0, R(1, 4), R(1, 4)]))
SIGNS = tuple(sp.Matrix(v) for v in product((-1, 1), repeat=3))
FULL = S * sp.Matrix([[1, 0, 0], [0, 1, 0], [R(1, 2), 0, R(1, 2)]])
MATCH = S * sp.Matrix([[1, 0, 0], [1, R(1, 2), 0], [0, R(1, 2), 0]])
EXACT_ALPHA = sp.diag(S, S, 0)


def eq(a, b):
    if isinstance(a, sp.MatrixBase):
        assert (a-b).applyfunc(sp.simplify) == sp.zeros(*a.shape)
    else:
        assert sp.simplify(a-b) == 0


def variance(j):
    omega = j*j.T
    return tuple((d.T*omega*d)[0] for d in D)


def margins(theta):
    return tuple((d.T*theta)[0] for d in D)


def score(a, p, theta):
    return a*(theta[0]+theta[2])+p*theta[1]


def domain_points(j):
    return [c+j*v for c in C for v in SIGNS] + [*C, (C[0]+C[1])/2]


def check_geometry():
    # Independently maximize the score over all three funded vertices.
    for j in (FULL, MATCH, EXACT_ALPHA):
        assert sum(x*x for x in j) <= R(1, 10000)
        for theta in domain_points(j):
            etf = max(score(0, 0, theta), score(0, 1, theta))
            full = max(score(a, p, theta) for a, p in ((0, 0), (0, 1), (1, 0)))
            eq(full-etf, max(0, min(margins(theta))))
            eq(score(1, 0, theta)-etf, min(margins(theta)))
            for a in (R(1, 4), R(1, 2), R(1)):
                for p in (0, (1-a)/2, 1-a):
                    assert score(a, p, theta)-etf <= a*min(margins(theta))
            for u in SIGNS:
                x = theta+j*u
                assert 1+x[0]+x[2] > 0 and 1+x[1] > 0
        assert C[0][1] < 0 < C[1][1]
    # Symbolic covariance expansion and an exactly noiseless ETF contrast.
    v11, v22, v33, v12, v13, v23 = sp.symbols('v11 v22 v33 v12 v13 v23')
    omega = sp.Matrix([[v11, v12, v13], [v12, v22, v23], [v13, v23, v33]])
    eq((D[0].T*omega*D[0])[0], v11+2*v13+v33)
    eq((D[1].T*omega*D[1])[0], v11+v22+v33-2*v12+2*v13-2*v23)
    eq(D[1].T*MATCH, sp.zeros(1, 3))
    assert variance(MATCH) == (5*S*S/4, 0)
    assert variance(EXACT_ALPHA) == (S*S, 2*S*S)
    # Precise alpha never removes this independent unspanned-premium error.
    for tau in (0, R(1, 100), R(1, 2), 1):
        j = sp.diag(S, S, S*tau)
        assert max(variance(j)) >= S*S
    print('Exact funded geometry and cross-covariance examples passed.')


def sine_law(k):
    phi = sp.pi/(4*k)
    roots = [sp.sin(i*phi) for i in range(1, 4*k)]
    q = [sp.simplify(x*x/(2*k)) for x in roots]
    z = [i-2*k for i in range(1, 4*k)]
    eq(sum(q), 1)
    eq(sum(p*x for p, x in zip(q, z)), 0)
    v = sp.simplify(sum(p*x*x for p, x in zip(q, z)))
    assert v >= R(k*k, 16) and v <= 4*k*k
    eq(sum(p*x*x/v for p, x in zip(q, z)), 1)
    assert max(x*x/v for x in z) <= 64
    # Positive sine amplitudes give exact square roots of the masses.
    affinity = sum(a*b for a, b in zip(roots, roots[1:]))/(2*k)
    eq(sp.trigsimp(affinity), sp.cos(phi))
    # The latent shifted supports overlap precisely at adjacent grid atoms.
    shifted_minus = [R(2*x-1, 2) for x in z]
    shifted_plus = [R(2*x+1, 2) for x in z]
    assert shifted_minus[1:] == shifted_plus[:-1]
    return q, z, v


def hard_fixtures():
    # These bases are explicit, independent of the proof's existence argument.
    return (
        (FULL, 1, sp.Matrix([3, -2, 1])/sp.sqrt(14),
         sp.Matrix([2, 3, 0])/sp.sqrt(13), sp.Matrix([-3, 2, 13])/sp.sqrt(182)),
        (MATCH, 0, sp.Matrix([2, 1, 0])/sp.sqrt(5),
         sp.Matrix([-1, 2, 0])/sp.sqrt(5), sp.Matrix([0, 0, 1])),
        (EXACT_ALPHA, 1, sp.Matrix([1, -1, 0])/sp.sqrt(2),
         sp.Matrix([1, 1, 0])/sp.sqrt(2), sp.Matrix([0, 0, 1])),
    )


def check_hard_law():
    for k in (2, 3):
        sine_law(k)
    q, z, v = sine_law(2)
    a = 1/(2*sp.sqrt(v))
    for j, face, h, v1, v2 in hard_fixtures():
        basis = sp.Matrix.hstack(h, v1, v2)
        eq(basis.T*basis, sp.eye(3))
        omega = j*j.T
        sigma = sp.sqrt(max(variance(j)))
        eq(j.T*D[face], sigma*h)
        delta = sigma/8  # k=floor(sigma/(4 delta))=2.
        latent_mean = sp.zeros(3, 1)
        latent_second = sp.zeros(3, 3)
        for p, x in zip(q, z):
            for s1, s2 in product((-1, 1), repeat=2):
                # Coordinates in the basis; transform the exact moments below.
                u = sp.Matrix([x/sp.sqrt(v), s1, s2])
                latent_mean += p*u/4
                latent_second += p*u*u.T/4
                assert sp.simplify(u.dot(u)) <= 81
        eq(basis*latent_mean, sp.zeros(3, 1))
        eq(j*basis*latent_second*basis.T*j.T, omega)
        theta_minus, theta_plus = C[face]-a*j*h, C[face]+a*j*h
        assert all(sp.simplify((a*x)**2) <= 1 for x in h)
        eq(margins(theta_minus)[face], -a*sigma)
        eq(margins(theta_plus)[face], a*sigma)
        assert sp.simplify(margins(theta_plus)[1-face]-a*sigma) > 0
        assert sp.simplify(a*sigma-delta) >= 0
        if j == EXACT_ALPHA:
            eq(theta_minus[2], theta_plus[2])
        # Verify the common latent-to-public map for both hypotheses.
        for sign in (-1, 1):
            theta = C[face]+sign*a*j*h
            u = h*z[0]/sp.sqrt(v)+v1-v2
            eq(theta+j*u, C[face]+j*(h*(z[0]/sp.sqrt(v)+sign*a)+v1-v2))
    print('Exact normalized sine laws and full-rank/singular embeddings passed.')


def public_hard_law(j, face, h, v1, v2, sign, q, z, v):
    law = defaultdict(lambda: sp.S.Zero)
    for mass, x in zip(q, z):
        for s1, s2 in product((-1, 1), repeat=2):
            observed = C[face]+j*(h*(x+R(sign, 2))/sp.sqrt(v)+v1*s1+v2*s2)
            # Full observable (f1,f2,rA,rE); no latent scenario label retained.
            record = tuple(sp.expand(t) for t in
                           (observed[0], observed[1], observed[0]+observed[2], observed[1]))
            law[record] += mass/4
    return {record: sp.expand(mass) for record, mass in law.items()}


def likelihood_bins(p, q):
    # Merge identical (null mass, alternative mass) pairs, retaining multiplicity.
    bins = defaultdict(int)
    for record in p.keys() | q.keys():
        bins[(p.get(record, 0), q.get(record, 0))] += 1
    return dict(bins)


def product_bins(one_record, count):
    out = {(sp.S.One, sp.S.One): 1}
    for _ in range(count):
        new = defaultdict(int)
        for (p, q), multiplicity in out.items():
            for (r, s), copies in one_record.items():
                new[(sp.expand(p*r), sp.expand(q*s))] += multiplicity*copies
        out = dict(new)
    return out


def optimal_endpoint_power(bins, epsilon):
    # Exact finite fractional-knapsack solution, not a sample-mean test.
    # Exchange of rejection mass from lower to higher q/p proves optimality.
    power = sum(m*q for (p, q), m in bins.items() if p == 0)
    ranked = sorted(((sp.simplify(q/p), m*p, m*q)
                     for (p, q), m in bins.items() if p != 0 and q != 0),
                    key=lambda item: item[0], reverse=True)
    budget = epsilon
    for _, cost, benefit in ranked:
        if budget == 0:
            break
        take = min(sp.S.One, sp.simplify(budget/cost))
        budget = sp.simplify(budget-take*cost)
        power = sp.simplify(power+take*benefit)
    assert budget >= 0
    return power


def check_public_testing():
    q, z, v = sine_law(2)
    epsilon = R(1, 16)
    scalar_minus = {R(2*x-1, 2): p for x, p in zip(z, q)}
    scalar_plus = {R(2*x+1, 2): p for x, p in zip(z, q)}
    scalar_bins = likelihood_bins(scalar_minus, scalar_plus)
    for j, face, h, v1, v2 in hard_fixtures():
        p = public_hard_law(j, face, h, v1, v2, -1, q, z, v)
        alt = public_hard_law(j, face, h, v1, v2, 1, q, z, v)
        eq(sum(p.values()), 1)
        eq(sum(alt.values()), 1)
        # The singular fixtures collapse pairs of latent scenarios; probabilities
        # must be combined before any testing calculation is meaningful.
        assert len(p) == len(alt) == (28 if j == FULL else 14)
        bins = likelihood_bins(p, alt)
        # Aggregate affinity by mass pair for inexpensive exact radicals.
        affinity = sp.simplify(sum(m*sp.sqrt(a*b) for (a, b), m in bins.items()))
        eq(sp.simplify(affinity**2), sp.cos(sp.pi/8)**2)
        for count in (1, 2):
            histories = product_bins(bins, count)
            eq(sum(m*a for (a, b), m in histories.items()), 1)
            eq(sum(m*b for (a, b), m in histories.items()), 1)
            power = optimal_endpoint_power(histories, epsilon)
            scalar_power = optimal_endpoint_power(product_bins(scalar_bins, count), epsilon)
            eq(power, scalar_power)
            # Even the endpoint-only relaxation cannot attain the claim's power
            # requirement at these lengths. Uniform validity is more restrictive.
            assert power < 1-epsilon
            assert sp.simplify(affinity**(2*count)) > 4*epsilon*(1-epsilon)
    print('Exact full-public-record testing passed: merged singular atoms and N_obs=1,2 endpoint optima.')


def check_certificate():
    epsilon, count = R(1, 16), 2
    for j in (FULL, MATCH, EXACT_ALPHA):
        omega = j*j.T
        inverse = omega.pinv()
        projector = j.T*inverse*j
        eq(projector*projector, projector)
        eq(projector.T, projector)
        variances = variance(j)
        errors = defaultdict(lambda: sp.S.Zero)
        for u, v in product(SIGNS, repeat=2):
            errors[tuple(j*(u+v)/2)] += R(1, 64)
        statistics = defaultdict(lambda: sp.S.Zero)
        for error, mass in errors.items():
            e = sp.Matrix(error)
            statistics[count*(e.T*inverse*e)[0]] += mass
        coverage = 0
        for critical in sorted(statistics):
            coverage += statistics[critical]
            if coverage >= 1-epsilon:
                break
        assert coverage >= 1-epsilon
        # Exact support radii for the ambient ellipsoid, before domain clipping.
        penalties = [sp.sqrt(critical*s2/count) for s2 in variances]
        positive_covered = 0
        for theta in domain_points(j):
            for error, mass in errors.items():
                e = sp.Matrix(error)
                statistic = count*(e.T*inverse*e)[0]
                if statistic > critical:
                    continue  # No assertion of domain intersection off coverage.
                estimate = theta+e
                lower = min(x-p for x, p in zip(margins(estimate), penalties))
                actual = min(margins(theta))
                assert sp.simplify(actual-lower) >= 0
                bound = min(x-2*p for x, p in zip(margins(theta), penalties))
                assert sp.simplify(lower-bound) >= 0
                if lower > 0:
                    assert score(1, 0, estimate) > max(0, estimate[1])
                if theta == (C[0]+C[1])/2:
                    assert lower > 0
                    positive_covered += mass
                # Any of these domain points in C_N must also obey ell<=Adv.
                for candidate in domain_points(j):
                    diff = estimate-candidate
                    if omega*inverse*diff != diff:
                        continue
                    if count*(diff.T*inverse*diff)[0] <= critical:
                        assert sp.simplify(min(margins(candidate))-lower) >= 0
        assert positive_covered == coverage
    print('Exact two-record directional certificates passed, with nonvacuous coverage.')


if __name__ == '__main__':
    check_geometry()
    check_hard_law()
    check_public_testing()
    check_certificate()
    print('Claim 016 checks passed; general bounds and quantifiers remain paper proofs.')
