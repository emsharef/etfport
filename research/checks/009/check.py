"""Fixed exact checks of claim 009 against direct quadratic optimization.

No optimizer or experiment code imported. Enumerate vertices and edge maxima
in each of the four trade-sign polygons; also test any interior stationary point.
All data are assumed, all arithmetic rational; this is not the general proof.
Run: uv run python checks/009/check.py
"""
from fractions import Fraction as F
from itertools import combinations, product

Z, O = F(0), F(1)


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def matvec(a, x):
    return tuple(dot(row, x) for row in a)


def solve2(a, b, rhs):
    det = a[0]*b[1] - a[1]*b[0]
    if det == 0:
        return None
    return ((rhs[0]*b[1]-a[1]*rhs[1])/det,
            (a[0]*rhs[1]-rhs[0]*b[0])/det)


def tau(d, w):
    return sum(kp*max(x-old, Z) + km*max(old-x, Z)
               for x, old, kp, km in zip(w, d['start'], d['buy'], d['sell']))


def cash(d, w):
    return O-sum(w)-tau(d, w)


def score(d, w, x):
    means = (d['mean']+x, d['mean'])
    return dot(means, w)-d['gamma']*dot(w, matvec(d['sigma'], w))/2-tau(d, w)


def optimum(d, x, etf_only=False):
    """Independent primal maximization over a compact two-dimensional polygon.

    Singular quadratics have a maximizing point on a boundary unless constant;
    a linear/constant edge is maximized at an endpoint. All vertex pairs include
    the actual edges and remain feasible by convexity, including zero-width boxes.
    """
    h = tuple(tuple(d['gamma']*v for v in row) for row in d['sigma'])
    all_candidates = set()
    for signs in product((-1, 1), repeat=2):
        c = tuple(kp if s > 0 else -km for s, kp, km in zip(signs, d['buy'], d['sell']))
        amin, amax = (d['start'][0],)*2 if etf_only else (Z, d['caps'][0])
        constraints = [((-O, Z), -amin), ((O, Z), amax),
                       ((Z, -O), Z), ((Z, O), d['caps'][1]),
                       ((O+c[0], O+c[1]), O+dot(c, d['start']))]
        for i, s in enumerate(signs):
            normal = tuple(F(-s) if j == i else Z for j in range(2))
            constraints.append((normal, -s*d['start'][i]))

        def feasible(w):
            return all(dot(a, w) <= b for a, b in constraints)

        vertices = set()
        for (a, arhs), (b, brhs) in combinations(constraints, 2):
            point = solve2(a, b, (arhs, brhs))
            if point is not None and feasible(point):
                vertices.add(point)
        candidates = set(vertices)
        linear = (d['mean']+x-c[0], d['mean']-c[1])
        for v, w in combinations(vertices, 2):
            delta = tuple(y-z for y, z in zip(w, v))
            curvature = dot(delta, matvec(h, delta))
            if curvature > 0:
                marginal = dot(tuple(y-z for y, z in zip(linear, matvec(h, v))), delta)
                t = min(O, max(Z, marginal/curvature))
                candidates.add(tuple(z+t*y for z, y in zip(v, delta)))
        stationary = solve2(h[0], h[1], linear)
        if stationary is not None and feasible(stationary):
            candidates.add(stationary)
        all_candidates.update(candidates)
    assert all_candidates
    values = [(score(d, w, x), w) for w in all_candidates]
    return max(values)


def interval(d, w):
    p, old, cap = w[1], d['start'][1], d['caps'][1]
    kp, km = d['buy'][1], d['sell'][1]
    ell, upper = (kp, kp) if p > old else (-km, -km) if p < old else (-km, kp)
    g = d['mean']-d['gamma']*matvec(d['sigma'], w)[1]
    lo, hi = Z, None
    if p < cap:
        lo = max(lo, (g-upper)/(O+upper))
    if p > 0:
        hi = (g-ell)/(O+ell)
    if cash(d, w) > 0:
        assert lo <= 0 and (hi is None or hi >= 0)
        lo, hi = Z, Z
    assert hi is None or lo <= hi
    return lo, hi


def data(start=(F(1, 2), F(1, 2)), caps=(O, O), mean=F(1, 50),
         buy=(F(1, 100), Z), sell=(F(1, 50), Z), gamma=O, zero_shocks=False):
    shocks = ((Z, Z),) if zero_shocks else tuple(
        (F(f, 10)+F(a, 50), F(f, 10)+F(e, 100))
        for f, a, e in product((-1, 1), repeat=3))
    sigma = tuple(tuple(sum(s[i]*s[j] for s in shocks)/len(shocks)
                        for j in range(2)) for i in range(2))
    return dict(start=start, caps=caps, mean=mean, buy=buy, sell=sell,
                gamma=gamma, shocks=shocks, sigma=sigma)


def check(name, d, expected_interval=None):
    assert all(0 <= old <= cap <= 1 for old, cap in zip(d['start'], d['caps']))
    assert sum(d['start']) <= 1
    assert all(0 <= k < 1 for k in d['buy']+d['sell'])
    _, w = optimum(d, Z, True)
    lo, hi = interval(d, w)
    if expected_interval is not None:
        assert (lo, hi) == expected_interval
    a0, cap = d['start'][0], d['caps'][0]
    center = d['gamma']*matvec(d['sigma'], w)[0]-d['mean']
    lower = center-d['sell'][0]+(1-d['sell'][0])*lo
    upper = None if hi is None else center+d['buy'][0]+(1+d['buy'][0])*hi
    assert a0 == 1 or hi is not None
    step = F(1, 100000)
    points = {F(-1, 2), Z, F(1, 2), lower-step, lower, lower+step}
    if upper is not None:
        points.update((upper-step, upper, upper+step, (lower+upper)/2))
    alpha_min = max(-1-d['mean']-shock[0] for shock in d['shocks'])
    points.update((alpha_min, alpha_min+step))
    base_etf, _ = optimum(d, Z, True)
    for x in points:
        actual_full, _ = optimum(d, x)
        actual_etf, _ = optimum(d, x, True)
        assert actual_etf == base_etf+x*a0
        predicted = (True if cap == 0 else x <= upper if a0 == 0
                     else x >= lower if a0 == cap else lower <= x <= upper)
        assert (actual_full == actual_etf) == predicted, (name, x, lo, hi)
        assert (score(d, w, x) == actual_full) == predicted
        positive = all(1+d['mean']+x+s[0] > 0 and 1+d['mean']+s[1] > 0
                       for s in d['shocks'])
        assert positive == (x > alpha_min)
    if 0 < a0 < cap:
        assert upper-lower == d['buy'][0]*(1+hi)+d['sell'][0]*(1+lo)+(hi-lo)
    print(f'PASS: {name}; multipliers [{lo}, {hi if hi is not None else "infinity"}]')


def main():
    check('interior active, asymmetric rates', data())
    check('ETF kink permits an interval', data(buy=(F(1, 100), F(1, 1000)),
                                             sell=(F(1, 50), F(1, 500))))
    check('slack cash', data(start=(F(1, 4), F(1, 4)), mean=F(201, 40000)), (Z, Z))
    check('binding cash and zero multiplier', data(mean=F(201, 20000)), (Z, Z))
    check('active lower bound', data(start=(Z, O)))
    check('active upper bound below one', data(caps=(F(1, 2), O)))
    check('active fixed at zero', data(start=(Z, F(1, 2)), caps=(Z, O)))
    check('ETF fixed at zero', data(start=(F(1, 2), Z), caps=(O, Z)), (Z, Z))
    check('fully active incumbent, unbounded interval',
          data(start=(O, Z), mean=Z, buy=(Z, Z), sell=(Z, Z), gamma=Z, zero_shocks=True),
          (Z, None))
    check('nonunique optima, collapsed band',
          data(mean=Z, buy=(Z, Z), sell=(Z, Z), gamma=Z, zero_shocks=True), (Z, Z))
    print('PASS: exact primal class maxima agree with all fixed band cases; no general proof claimed.')


if __name__ == '__main__':
    main()
