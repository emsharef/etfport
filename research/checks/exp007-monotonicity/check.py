"""Independent exact checks of two registered experiment-007 witnesses (M2).

No experiment solver, certificate routine or reported JSON is imported.
These fixed-instance checks are not a grid reproduction or a general theorem.
"""
from fractions import Fraction as F
from itertools import product

prior = tuple(product((F(3, 200), F(1, 40)), (F(-1, 400), F(1, 400))))
shocks = tuple((s1*F(3, 50)+s2*F(1, 100)+sa*F(3, 100),
                s1*F(3, 50)+se*F(1, 200))
               for s1, s2, sa, se, unused in product((-1, 1), repeat=5))
means = tuple((lam+F(1, 400)+alpha, lam+F(1, 10000)) for lam, alpha in prior)
mu = tuple(sum(m[i] for m in means)/len(means) for i in range(2))
S = tuple(tuple(sum(z[i]*z[j] for z in shocks)/len(shocks) for j in range(2))
          for i in range(2))
assert all(sum(z[i] for z in shocks) == 0 for i in range(2))
assert all(1+m[i]+z[i] > 0 for m, z in product(means, shocks) for i in range(2))
assert S[0][0] > 0 and S[0][0]*S[1][1]-S[0][1]**2 > 0


def gradient(w):
    return tuple(mu[i]-sum(S[i][j]*w[j] for j in range(2)) for i in range(2))


def cash(w, old, rate):
    return 1-sum(w)-rate*sum(abs(w[i]-old[i]) for i in range(2))


# H2: active initially absent; cash replaces initial ETF holdings, at fixed wealth.
rate = F(1, 2000)
active = []
for c in (F(0), F(1, 4)):
    old = (F(0), 1-c)
    a = (1-rate*(1-c))/(1+rate)  # all cash plus net ETF proceeds buy the active fund
    w = (a, F(0))
    assert 0 < a < 1 and cash(w, old, rate) == 0
    g = gradient(w)
    eta = (g[0]-rate)/(1+rate)
    slopes = (rate, -rate)  # active purchase, ETF sale
    residual = tuple(g[i]-eta-(1+eta)*slopes[i] for i in range(2))
    assert eta > 0 and residual[0] == 0 and residual[1] < 0
    # The concave Lagrangian supports Q at w; its residual is zero on the free
    # active coordinate and negative on the lower ETF bound. Complementarity
    # gives global optimality, and positive-definite S gives uniqueness.
    active.append(a)
assert active == [F(1999, 2001), F(7997, 8004)]
assert active[1]-active[0] == F(1, 8004)
print('H2 unique active holdings:', *(str(a) for a in active), '; increase = 1/8004')

# H3: active incumbent 1/2, ETF incumbent 0, cash 1/2; ETF cap 1/2.
widths = []
for rate in (F(0), F(1, 2000)):
    old = (F(1, 2), F(0))
    p = F(1, 2)/(1+rate)
    w = (old[0], p)
    assert p <= F(1, 2) and cash(w, old, rate) == 0
    g = gradient(w)
    assert g[1]-rate > 0  # ETF-only objective increasing up to this feasible endpoint
    # At the cap only the lower stationarity inequality survives; below the cap
    # both inequalities impose equality. These are claim 009's defining inequalities.
    hi = (g[1]-rate)/(1+rate)
    lo = F(0) if p == F(1, 2) else hi
    alpha_c = sum(S[0][j]*w[j] for j in range(2))-mu[0]
    lower = alpha_c-rate+(1-rate)*lo
    upper = alpha_c+rate+(1+rate)*hi
    assert lower <= upper
    # All translated-alpha scenarios at these endpoints remain M2 admissible.
    assert all(1+m[0]+z[0]+endpoint > 0
               for m, z, endpoint in product(means, shocks, (lower, upper)))
    width = upper-lower
    assert width == rate*(1+hi)+rate*(1+lo)+(hi-lo)
    widths.append(width)
    print(f'H3 rate={rate}: p={p}, I=[{lo}, {hi}], C=[{lower}, {upper}], width={width}')
assert widths == [F(1319, 80000), F(701377, 690345000)]
assert widths[1] < widths[0]
print('PASS: two exact assumed-instance refutations; no full-grid reproduction asserted')
