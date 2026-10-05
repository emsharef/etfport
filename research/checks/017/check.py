"""Exact finite checks for claim 017; not the arbitrary-law rate proof.

Run: uv run python checks/017/check.py
The gate check sums all three-coordinate binomial count classes, with no
simulation, asymptotic quantile, solver tolerance, or floating-point decision.
"""
from collections import defaultdict
from itertools import product
from math import comb

import sympy as sp

R = sp.Rational


def zero(expr):
    assert sp.simplify(expr) == 0


def check_geometry():
    a, p, x, lam = sp.symbols('a p x lam', real=True)
    score = a*x+p*lam-a*a-p*p/2
    zero(score-lam*lam/2-(a*x-a*a-(p-lam)**2/2))
    zero(score.subs({a: x/2, p: lam})-lam*lam/2-x*x/4)
    for s in (R(1, 100), R(1, 1000)):
        for t1, t2, t3 in product((-1, 0, 1), repeat=3):
            mean = s*(t1+t3)
            premium = R(1, 4)+s*t2
            active = max(mean, 0)/2
            assert 0 < premium < 1 and active+premium < 1
            # The unconstrained coordinate maxima are feasible, hence global.
            assert sp.diff(score, p).subs({p: premium, lam: premium}) == 0
            assert sp.diff(score, a).subs({a: active, x: mean}) <= 0
        assert R(1, 4)-10*s >= R(3, 20)
        assert R(1, 4)+10*s+8*s < 1
        assert (2+9*sp.sqrt(2))*s < 16*s
        assert 1-(2+9*sp.sqrt(2))*s > 0
    # Independently check the certificate's increasing quadratic at the worst
    # covered active holding and the stated radius-to-margin boundary.
    r, d = sp.symbols('r d', positive=True)
    lower_a = sp.sqrt(d)-r/sp.sqrt(2)
    bound = lower_a**2-sp.sqrt(2)*r*lower_a-r*r/2
    zero(bound-(d-2*sp.sqrt(2)*r*sp.sqrt(d)+r*r))
    assert sp.simplify(bound.subs(r, sp.sqrt(d)/8)-5*d/8) > 0
    print('Exact funded quadratic geometry, plug-in bounds, and certificate algebra passed.')


def check_hard_pair():
    h = sp.Matrix([1, 0, 1])/sp.sqrt(2)
    v1, v2 = sp.Matrix([0, 1, 0]), sp.Matrix([1, 0, -1])/sp.sqrt(2)
    basis = sp.Matrix.hstack(h, v1, v2)
    assert basis.T*basis == sp.eye(3)
    s = R(1, 1000)
    for k in (2, 3):
        q = [sp.simplify(sp.sin(i*sp.pi/(4*k))**2/(2*k)) for i in range(1, 4*k)]
        z = [i-2*k for i in range(1, 4*k)]
        zero(sum(q)-1)
        zero(sum(p*w for p, w in zip(q, z)))
        variance = sp.simplify(sum(p*w*w for p, w in zip(q, z)))
        shift = 1/(2*sp.sqrt(variance))
        delta = s*s/(32*k*k)
        zero(s/(4*sp.sqrt(2*delta))-k)
        assert delta <= s*s/128
        assert sp.simplify(shift*shift) <= 1
        for sign in (-1, 1):
            theta = sp.Matrix([0, R(1, 4), 0])+sign*shift*s*h
            mean = sp.simplify(theta[0]+theta[2])
            assert abs(theta[0]) <= s and abs(theta[2]) <= s
            if sign < 0:
                assert mean < 0
            else:
                assert sp.simplify(mean*mean/4-delta) >= 0
                assert mean/2+theta[1] < 1
        # Compute risky-return covariance from the actual loading map.
        latent_covariance = sp.diag(sp.simplify(sum(p*w*w/variance for p, w in zip(q, z))), 1, 1)
        fund_map = s*sp.Matrix([[1, 0, 1], [0, 1, 0]])*basis
        assert sp.simplify(fund_map*latent_covariance*fund_map.T) == sp.diag(2*s*s, s*s)
    print('Exact normalized hard pairs passed: fixed risk covariance and square-root mean separation.')


def check_finite_gate():
    # Uniform independent signs: all 2^(3N) ordered histories are represented
    # exactly by 65^3 count classes. Work in integer coordinates scaled by N/s.
    n = 64
    values = [(2*k-n, comb(n, k)) for k in range(n+1)]
    denominator = 2**(3*n)
    square_law = defaultdict(int)
    for z, weight in values:
        square_law[z*z] += weight
    statistic_law = {0: 1}
    for _ in range(3):
        new = defaultdict(int)
        for a, p in statistic_law.items():
            for b, q in square_law.items():
                new[a+b] += p*q
        statistic_law = dict(new)
    assert sum(statistic_law.values()) == denominator
    coverage_mass = 0
    for critical_square in sorted(statistic_law):
        coverage_mass += statistic_law[critical_square]
        if 16*coverage_mass >= 15*denominator:
            break
    check_separate_penalties(n, critical_square)
    # delta=s^2/128 and economic threshold delta/4. Multiplication by 4N^2/s^2
    # makes the threshold N^2/128 and every true score comparison integral.
    threshold = n*n//128
    assert n*n % 128 == 0
    certified = {}
    for holding_twice in range(4*n+1):
        lhs = holding_twice**2-2*critical_square-threshold
        certified[holding_twice] = (
            holding_twice > 0 and lhs > 0
            and lhs*lhs > 8*holding_twice**2*critical_square
        )
    # Domain points: a null, a negative signal, a near-boundary alternative,
    # and a larger alternative. ETF means also differ across these points.
    for truth in ((0, 0, 0), (-n, -n, -n), (n//8, n, n//8), (n, 0, n)):
        true_x = truth[0]+truth[2]
        false_mass = correct_mass = covered_mass = 0
        for (z1, p1), (z2, p2), (z3, p3) in product(values, repeat=3):
            mass = p1*p2*p3
            hats = (truth[0]+z1, truth[1]+z2, truth[2]+z3)
            distance_square = sum(max(abs(v)-n, 0)**2 for v in hats)
            nonempty = distance_square <= critical_square
            holding_twice = max(hats[0]+hats[2], 0)
            flag = nonempty and certified[holding_twice]
            actual = 2*holding_twice*true_x-holding_twice**2-2*z2*z2
            covered = z1*z1+z2*z2+z3*z3 <= critical_square
            assert not covered or nonempty
            assert not (covered and flag) or actual > threshold
            covered_mass += mass*covered
            false_mass += mass*(flag and actual <= threshold)
            correct_mass += mass*(flag and actual > threshold)
        assert covered_mass == coverage_mass
        assert 16*false_mass <= denominator
        if truth == (n, 0, n):
            # Nonvacuous certification, without asserting the arbitrary-law
            # sufficient sample condition is met at this small N.
            assert 16*correct_mass >= 15*denominator
    print('Exact 64-record gate passed: full binomial count classes, box intersection, false control and nonzero power.')


def check_separate_penalties(n, critical_square):
    # A predetermined balanced-history witness. Quantities below are divided
    # by s (holdings/errors) or s^2 (scores), so the same check holds for every
    # allowed s. Theta_hat=theta=(9s/16,1/4,9s/16); all three sign counts are N/2.
    assert n % 2 == 0 and comb(n, n//2)**3 > 0
    radius = sp.sqrt(critical_square)/n
    active = R(9, 16)
    threshold = R(1, 512)
    assert radius < 1-active  # The entire ball is inside the parameter box.
    assert sp.sqrt(2)*active >= radius
    # Exact global minimization: z=(e1+e3)/sqrt(2). The residual error obeys
    # e2^2 <= radius^2-z^2. The displayed factorization bounds its combined
    # penalty for every z in [-radius,radius], not only at a solver incumbent.
    z, r, a = sp.symbols('z r a', real=True)
    zero(sp.sqrt(2)*a*r-(sp.sqrt(2)*a*z+(r*r-z*z)/2)
         -(r-z)*(sp.sqrt(2)*a-(r+z)/2))
    # Equality is attained at e1=e3=radius/sqrt(2), e2=0, within that ball.
    errors = (radius/sp.sqrt(2), 0, radius/sp.sqrt(2))
    zero(sum(e*e for e in errors)-radius*radius)
    exact_target = active*active-sp.sqrt(2)*active*radius
    attained = active*(2*active-errors[0]-errors[2])-active*active-errors[1]**2/2
    zero(exact_target-attained)
    conservative = exact_target-radius*radius/2
    assert exact_target > threshold
    assert conservative <= threshold
    # All holdings, including the extremizing parameter's oracle ETF choice,
    # remain strictly funded and its lambda2 stays 1/4.
    assert active*R(1, 100)+R(1, 4) < 1
    print('Exact balanced-history witness passed: whole-class target certifies while the separate-penalty bound abstains.')


if __name__ == '__main__':
    check_geometry()
    check_hard_pair()
    check_finite_gate()
    print('Claim 017 finite checks passed; the uniform history rate remains a paper proof.')
