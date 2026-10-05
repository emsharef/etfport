"""Exact finite checks for claim 018; not its arbitrary-design/law proof.

Run: uv run python checks/018/check.py
Enumerate each cost-sign polygon and its interior, edges and vertices. A
strictly concave quadratic reaches its maximum at one of these candidates;
no numerical optimizer, Monte Carlo, or first-order interior assumption is used.
"""
from itertools import product, combinations

import sympy as sp

R = sp.Rational
A = sp.Matrix([[1, 0], [R(1, 2), 1], [1, 0]])
H = A.T*A  # gamma*Sigma with J=s I and gamma=1/s^2.
HINV = H.inv()
S = R(1, 100)
BUY = sp.Matrix([R(1, 50), R(3, 100)])
SELL = sp.Matrix([R(1, 100), R(1, 25)])
INC = sp.Matrix([R(2, 5), R(1, 2)])
CENTER = sp.Matrix([R(9, 10), 1, 0])


def eq(a, b):
    if isinstance(a, sp.MatrixBase):
        assert (a-b).applyfunc(sp.simplify) == sp.zeros(*a.shape)
    else:
        assert sp.simplify(a-b) == 0


def costs(w):
    return sum(BUY[i]*max(w[i]-INC[i], 0)+SELL[i]*max(INC[i]-w[i], 0)
               for i in range(2))


def cash(w):
    return 1-sum(w)-costs(w)


def score(w, theta):
    return (theta.T*A*w)[0]-(w.T*H*w)[0]/2-costs(w)


def solve(theta, cap, etf_only=False):
    candidates = set()
    for signs in product((-1, 1), repeat=2):
        slope = sp.Matrix([BUY[i] if signs[i] == 1 else -SELL[i] for i in range(2)])
        linear = A.T*theta-slope
        # Each constraint is normal'w<=bound.
        constraints = []
        for i in range(2):
            axis = sp.eye(2)[:, i]
            constraints.extend(((axis, cap[i]), (-axis, 0),
                                (-signs[i]*axis, -signs[i]*INC[i])))
        constraints.append((sp.ones(2, 1)+slope, 1+slope.dot(INC)))
        if etf_only:
            constraints.extend(((sp.Matrix([1, 0]), INC[0]),
                                (sp.Matrix([-1, 0]), -INC[0])))

        def keep(w):
            if all(normal.dot(w) <= bound for normal, bound in constraints):
                candidates.add(tuple(w))

        keep(HINV*linear)
        for normal, bound in constraints:
            anchor = normal*bound/normal.dot(normal)
            direction = sp.Matrix([-normal[1], normal[0]])
            t = direction.dot(linear-H*anchor)/(direction.T*H*direction)[0]
            keep(anchor+t*direction)
        for (v, b), (u, c) in combinations(constraints, 2):
            matrix = sp.Matrix.vstack(v.T, u.T)
            if matrix.det() != 0:
                keep(matrix.inv()*sp.Matrix([b, c]))
    assert candidates
    ranked = [(score(sp.Matrix(w), theta), w) for w in candidates]
    value, chosen = max(ranked)
    w = sp.Matrix(chosen)
    assert cash(w) >= 0 and all(0 <= w[i] <= cap[i] for i in range(2))
    if etf_only:
        assert w[0] == INC[0]
    assert sum(v == value for v, _ in ranked) == 1  # Unique distinct optimizer.
    return w, value


def check_geometry_and_certificates():
    # J=s I, Sigma=s^2 H. The generalized ratio K is exactly s^2:
    # (J'A)(gamma Sigma)^-1(A'J) is s^2 times this nonzero projection.
    projection = A*HINV*A.T
    eq(projection*projection, projection)
    assert projection == projection.T and projection.trace() == 2
    assert H.det() > 0 and H[0, 0] > 0 and H[0, 1] != 0
    k = S*S
    # For independent signs and N=1 the exact statistic is T=3 on every atom,
    # so r^2=3 at every eta in (0,1); all listed mean errors are covered.
    radius_squared = R(3)
    u = k*radius_squared
    buys = sells = binds_cash = binds_cap = positive_certificates = 0
    approximate_checks = negative_gaps = 0
    # A lower active mean gives a sale on the cash face; the higher mean gives
    # a purchase at the ETF-cap corner. These are test fixtures, not a sweep.
    fixtures = (
        (sp.Matrix([R(4, 5), R(9, 10)]), CENTER-sp.Matrix([R(1, 5), 0, 0])),
        (sp.Matrix([R(4, 5), R(11, 20)]), CENTER),
    )
    for cap, center in fixtures:
        true_full, true_full_value = solve(center, cap)
        true_etf, true_etf_value = solve(center, cap, True)
        true_gap = true_full_value-true_etf_value
        assert true_gap > 0
        for signs in product((-1, 1), repeat=3):
            error = S*sp.Matrix(signs)
            estimate = center+error
            w, vf = solve(estimate, cap)
            v, ve = solve(estimate, cap, True)
            gap = vf-ve
            difference = w-v
            assert gap >= (difference.T*H*difference)[0]/2
            lower = gap-sp.sqrt(2*u*gap)-u/2
            advantage = score(w, center)-true_etf_value
            assert sp.simplify(advantage-lower) >= 0
            assert sp.simplify(gap-(true_gap-sp.sqrt(2*u*true_gap)-u/2)) >= 0
            # Verify the intermediate full-ETF value bound independently.
            etf_bound = ve-(error.T*A*v)[0]+u/2
            assert etf_bound >= true_etf_value
            # Feasible approximate actions, with independently computed exact
            # global value gaps. Include an E candidate and negative score gaps.
            for wt, vt in (((w+INC)/2, (v+INC)/2),
                           (INC, (v+INC)/2), (w, (v+INC)/2),
                           ((w+INC)/2, v), (INC, v)):
                for point in (wt, vt):
                    assert cash(point) >= 0
                    assert all(0 <= point[i] <= cap[i] for i in range(2))
                assert vt[0] == INC[0]
                qf, qe = score(wt, estimate), score(vt, estimate)
                ef, ee, g = vf-qf, ve-qe, qf-qe
                assert ef >= 0 and ee >= 0 and g+ef >= 0
                lg = g-ee-sp.sqrt(2*u)*(sp.sqrt(ef)+sp.sqrt(g+ef))-u/2
                d = wt-vt
                ld = g-ee-sp.sqrt(u*(d.T*H*d)[0])-sp.sqrt(2*u*ee)-u/2
                actual = score(wt, center)-true_etf_value
                assert sp.simplify(actual-lg) >= 0
                assert sp.simplify(actual-ld) >= 0
                distance_bound = (sp.sqrt(ef)+sp.sqrt(g+ef))**2
                assert sp.simplify(distance_bound-(d.T*H*d)[0]/2) >= 0
                etf_approx_bound = qe-error.dot(A*vt)+ee+sp.sqrt(2*u*ee)+u/2
                assert sp.simplify(etf_approx_bound-true_etf_value) >= 0
                if wt[0] == INC[0]:
                    assert lg <= 0 and ld <= 0
                # Interval input conservatism, not a floating dual-gap solver.
                width = R(1, 10**8)
                interval_lower = (g-2*width-ee-sp.sqrt(2*u)*
                                  (sp.sqrt(ef)+sp.sqrt(g+2*width+ef))-u/2)
                assert sp.simplify(lg-interval_lower) >= 0
                approximate_checks += 1
                negative_gaps += int(bool(g < 0))
            # Positive lower bound certifies an active intervention, including sales.
            if lower > 0:
                assert w[0] != INC[0] and advantage > 0
                positive_certificates += 1
            buys += int(bool(w[0] > INC[0]))
            sells += int(bool(w[0] < INC[0]))
            binds_cash += int(cash(w) == 0)
            binds_cap += int(any(w[i] == cap[i] for i in range(2)))
        # Admissibility on a box containing every estimate and true parameter.
        for vertex in product((-1, 1), repeat=3):
            theta = center+2*S*sp.Matrix(vertex)
            for signs in product((-1, 1), repeat=3):
                realized = A.T*(theta+S*sp.Matrix(signs))
                assert all(1+value > 0 for value in realized)
    assert buys and sells and binds_cash and binds_cap and positive_certificates, (
        buys, sells, binds_cash, binds_cap, positive_certificates)
    assert approximate_checks == 80 and negative_gaps > 0
    print('80 approximate-action checks passed, including negative score gaps and score intervals.')
    print('Exact constrained certificates passed: purchases, sales, asymmetric fees, correlated risk, cash and cap faces.')



def check_shortcut_counterexamples():
    a = sp.Matrix([[1, 0], [0, 1], [1, 0]])
    h = a.T*a
    center = sp.Matrix([R(1, 2), R(1, 4), R(1, 2)])
    incumbent = sp.Matrix([R(2, 5), R(1, 4)])
    wt = sp.Matrix([R(3, 5), R(1, 4)])
    vbad = sp.Matrix([R(2, 5), R(7, 20)])

    def q(w, theta):
        return theta.dot(a*w)-(w.T*h*w)[0]/2

    # Completing squares gives the unconstrained optimum; it is funded.
    exact_w = h.inv()*a.T*center
    eq(exact_w, sp.Matrix([R(1, 2), R(1, 4)]))
    for w in (incumbent, exact_w, wt, vbad):
        assert all(0 <= t <= 1 for t in w) and sum(w) <= 1
    g = q(wt, center)-q(incumbent, center)
    ef = q(exact_w, center)-q(wt, center)
    eq(g, 0)
    eq(ef, R(1, 100))
    d = wt-incumbent
    eq((d.T*h*d)[0]/2, R(1, 25))
    assert (d.T*h*d)[0]/2 > g+ef
    theta = center-S*sp.ones(3, 1)
    true_v = sp.Matrix([incumbent[0], theta[1]])
    assert sum(true_v) < 1 and true_v[1] > 0
    advantage = q(wt, theta)-q(true_v, theta)
    eq(advantage, -R(81, 20000))
    u = 3*S*S
    shortcut = g-sp.sqrt(2*u*(g+ef))-u/2
    corrected = g-sp.sqrt(2*u)*(sp.sqrt(ef)+sp.sqrt(g+ef))-u/2
    eq(shortcut, -(20*sp.sqrt(6)+3)/20000)
    eq(corrected, -(40*sp.sqrt(6)+3)/20000)
    assert corrected <= advantage < shortcut
    ee = q(incumbent, center)-q(vbad, center)
    eq(ee, R(1, 200))
    loss = q(true_v, theta)-q(vbad, theta)
    eq(loss, R(121, 20000))
    eq(ee+u/2, R(103, 20000))
    assert ee+u/2 < loss <= ee+sp.sqrt(2*u*ee)+u/2
    # Every support point has T=3; the displayed theta is covered and its
    # all-positive shock yields exactly the displayed estimate.
    for signs in product((-1, 1), repeat=3):
        shock = S*sp.Matrix(signs)
        eq(shock.dot(shock)/(S*S), 3)
        for vertex in product((-1, 1), repeat=3):
            parameter = center+R(1, 10)*sp.Matrix(vertex)
            assert all(1+t > 0 for t in a.T*(parameter+shock))
    eq(theta+S*sp.ones(3, 1), center)
    print('Exact M4 counterexamples refute both suggested solver-gap shortcuts.')


def check_rate_algebra():
    delta = sp.symbols('delta', positive=True)
    u = delta/128
    first = sp.simplify(delta-sp.sqrt(2*u*delta)-u/2)
    eq(first, 223*delta/256)
    second = sp.simplify(3*delta/4-sp.sqrt(2*u*3*delta/4)-u/2)
    assert sp.simplify(second-delta/2) > 0
    # The lower-bound family has K=kappa exactly, not only an upper bound.
    lower_a = sp.Matrix([[1, 0], [0, 1], [1, 0]])
    for kappa in (R(1, 10000), R(1, 1000000)):
        sigma = kappa*sp.diag(2, 1)
        j = sp.sqrt(kappa)*sp.eye(3)
        eq(lower_a.T*j*j.T*lower_a, sigma)
        gamma = 1/kappa
        assert 1/gamma == kappa
    # A singular error representation, including score-irrelevant uncertainty.
    j = sp.diag(1, 0, 0)
    omega = j*j.T
    for y in (sp.Matrix([1, 2, 3]), sp.Matrix([-2, 1, 0])):
        e = j*y
        assert (e.T*omega.pinv()*e)[0] <= y.dot(y)
    null_direction = sp.Matrix([-1, 0, 1])
    assert A.T*null_direction == sp.zeros(2, 1)
    print('Exact power constants, lower-family normalization, and singular error algebra passed.')


if __name__ == '__main__':
    check_geometry_and_certificates()
    check_rate_algebra()
    check_shortcut_counterexamples()
    print('Claim 018 checks passed; the arbitrary-design/law result remains a paper proof.')
