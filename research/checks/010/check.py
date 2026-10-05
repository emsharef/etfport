"""Claim 010: exact finite-data and endpoint checks, not a general proof.

Run: uv run python checks/010/check.py
Reconstruct all 128 parameter/scenario pairs; independently compare the stated
band with experiment 004's primal active-set solver, without using its band code.
"""
from dataclasses import replace
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'experiments' / '004'))
from m2 import Instance2, check_instance, solve, sigma_formula  # noqa: E402

PRIOR = tuple(product((F(3, 200), F(1, 40)), (F(-1, 400), F(1, 400))))
SIGNS = tuple(product((-1, 1), repeat=5))
SHOCKS = tuple((3*F(s[0], 50)+F(s[1], 100)+3*F(s[2], 100),
                3*F(s[0], 50)+F(s[3], 200)) for s in SIGNS)
S = tuple(tuple(sum(z[i]*z[j] for z in SHOCKS)/32 for j in range(2)) for i in range(2))
assert S == ((F(23, 5000), F(9, 2500)), (F(9, 2500), F(29, 8000)))
assert all(sum(z[i] for z in SHOCKS) == 0 for i in range(2))
assert S[0][0]*S[1][1]-S[0][1]**2 == F(743, 200000000)
MU = (sum(lam+F(1, 400)+alpha for lam, alpha in PRIOR)/4,
      sum(lam+F(1, 10000) for lam, alpha in PRIOR)/4)
assert MU == (F(9, 400), F(201, 10000))
alpha_min = max(-1-lam-F(1, 400)-alpha-z[0]
                for (lam, alpha), z in product(PRIOR, SHOCKS))
assert alpha_min == F(-183, 200)
assert min(1+lam+F(1, 10000)+z[1]
           for (lam, alpha), z in product(PRIOR, SHOCKS)) == F(9501, 10000)

TABLE = (
    (F(0), F(1, 2), F(0), F(1319, 80000), F(-23, 1250),
     F(-23, 1250), F(-153, 80000), F(1319, 80000)),
    (F(1, 2000), F(1000, 2001), F(11032, 690345), F(11032, 690345), F(-61367, 3335000),
     F(-808663, 276138000), F(-38269, 20010000), F(701377, 690345000)),
)
probe_count = 0
for rate, p, lo, hi, center, lower, upper, width in TABLE:
    I = Instance2(BA=(F(1), F(1, 2)), BE=((F(1), F(0)),),
                  sf=(F(3, 50), F(1, 50)), sA=F(3, 100), sE=(F(1, 200),),
                  lam=(F(1, 50), F(1, 200)), alpha=F(0), cE=(F(-1, 10000),),
                  gamma=F(1), kbuy=(rate, rate), ksell=(rate, rate),
                  w0=(F(1, 2), F(0)), k0=F(1, 2), wbar=(F(1), F(1, 2)))
    assert not check_instance(I)
    assert tuple(map(tuple, sigma_formula(I))) == S
    for lam, alpha in PRIOR:
        assert not check_instance(replace(I, lam=(lam, F(1, 200)), alpha=alpha))
    value, w, candidates = solve(I, 'E')
    assert w == [F(1, 2), p] and len(candidates) == 1
    assert p == F(1, 2)/(1+rate)
    assert F(1, 2)-(1+rate)*p == 0
    g = MU[1]-S[1][0]/2-S[1][1]*p
    assert g-rate > 0
    assert hi == (g-rate)/(1+rate)
    assert lo == (F(0) if p == F(1, 2) else hi)
    assert center == S[0][0]/2+S[0][1]*p-MU[0]
    assert lower == center-rate+(1-rate)*lo
    assert upper == center+rate+(1+rate)*hi
    assert upper-lower == width == rate*(1+hi)+rate*(1+lo)+(hi-lo)
    assert alpha_min < F(-1, 50) < lower < upper < 0
    epsilon = F(1, 100000000)
    for x in (lower-epsilon, lower, lower+epsilon, upper-epsilon, upper, upper+epsilon,
              (lower+upper)/2, F(0)):
        assert all(1+lam+F(1, 400)+alpha+x+z[0] > 0
                   for (lam, alpha), z in product(PRIOR, SHOCKS))
        _, full, optima = solve(replace(I, alpha=x), 'F')
        assert len(optima) == 1
        assert (full[0] == F(1, 2)) == (lower <= x <= upper)
        probe_count += 1
    print(f'PASS rate={rate}: E={w}, I=[{lo},{hi}], C=[{lower},{upper}], width={width}')
assert TABLE[0][-1]-TABLE[1][-1] == F(170890979, 11045520000) > 0
print(f'PASS: finite model validity, exact table and {probe_count} primal optimizer probes')
