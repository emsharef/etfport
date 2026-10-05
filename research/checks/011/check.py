"""Claim 011 fixed-instance checks; not a proof of existence or general concavity.

Run: uv run python checks/011/check.py
Uses the nontrivial M3 witness; mixes complete observable policy vectors, rather
than recomputing a feedback rule at mixed states. Funding and wealth are rational;
only exponential utility uses floats. No optimization results are asserted.
"""
from fractions import Fraction as F
from itertools import product
from math import exp
from pathlib import Path
import importlib.util

path = Path(__file__).resolve().parents[1] / 'm3-definition' / 'check.py'
spec = importlib.util.spec_from_file_location('m3_fixed_data', path)
m3 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m3)

Y = set(m3.observation(theta, signs) for theta, signs in product(m3.THETA, m3.SIGNS))
M = max(F(1), *(1+r for y in Y for r in y[1]))
ZERO = (F(0), F(0))


def blend(first, second, t):
    return tuple(t*a+(1-t)*b for a, b in zip(first, second))


def choose(state, label, variant):
    if label == 'N':
        return ZERO
    i = 0 if label == 'F' else 1
    trade = list(ZERO)
    if variant == 0:
        trade[i] = -state[0][i]/3
    else:
        trade[i] = state[1]/(3*(1+m3.BUY[i]))
    return tuple(trade)


def policy(root_label, future_label, variant):
    root = choose(m3.INITIAL, root_label, variant)
    root_post = m3.review(m3.INITIAL, root)
    nodes = {y: choose(m3.mark(root_post, y), future_label, variant) for y in Y}
    return root, nodes


def states(pol, root_label, future_label):
    root, nodes = pol
    if root_label == 'E':
        assert root[0] == 0
    if root_label == 'N':
        assert root == ZERO
    assert set(nodes) == Y
    root_post = m3.review(m3.INITIAL, root)
    assert 0 < sum(root_post[0])+root_post[1] <= m3.W0
    assert all(abs(u) <= m3.W0 for u in root)
    incoming, outgoing = {}, {}
    for y in Y:
        incoming[y] = m3.mark(root_post, y)
        assert 0 < sum(incoming[y][0])+incoming[y][1] <= M*m3.W0
        if future_label == 'E':
            assert nodes[y][0] == 0
        if future_label == 'N':
            assert nodes[y] == ZERO
        outgoing[y] = m3.review(incoming[y], nodes[y])
        assert 0 < sum(outgoing[y][0])+outgoing[y][1] <= M*m3.W0
        assert all(abs(u) <= M*m3.W0 for u in nodes[y])
    return root_post, incoming, outgoing


mixtures = 0
for D, R in product(('N', 'E', 'F'), repeat=2):
    first, second = policy(D, R, 0), policy(D, R, 1)
    a0, ai, ao = states(first, D, R)
    b0, bi, bo = states(second, D, R)
    for t in (F(0), F(1, 3), F(1, 2), F(1)):
        mixed = (blend(first[0], second[0], t),
                 {y: blend(first[1][y], second[1][y], t) for y in Y})
        c0, ci, co = states(mixed, D, R)
        assert c0[0] == blend(a0[0], b0[0], t)
        assert c0[1] >= t*a0[1]+(1-t)*b0[1]
        for y in Y:
            assert ci[y][0] == blend(ai[y][0], bi[y][0], t)
            assert ci[y][1] >= t*ai[y][1]+(1-t)*bi[y][1]
            assert co[y][0] == blend(ao[y][0], bo[y][0], t)
            assert co[y][1] >= t*ao[y][1]+(1-t)*bo[y][1]
            # Stronger than checking only posterior-positive paths: every
            # observation is crossed with all terminal parameters/scenarios.
            for theta, signs in product(m3.THETA, m3.SIGNS):
                wa = m3.terminal(ao[y], theta, signs)
                wb = m3.terminal(bo[y], theta, signs)
                wc = m3.terminal(co[y], theta, signs)
                assert 0 < wc <= M*M*m3.W0
                assert wc >= t*wa+(1-t)*wb
                ua, ub, uc = (-exp(-float(m3.RHO*w/m3.W0)) for w in (wa, wb, wc))
                assert uc+1e-14 >= float(t)*ua+float(1-t)*ub
        mixtures += 1

# The zero-state extension used in the joint-concavity statement has zero trade
# and utility -1; at positive wealth, liquidating all risky positions leaves cash.
assert m3.review((ZERO, F(0)), ZERO) == (ZERO, F(0))
for state in (((F(1), F(0)), F(0)), ((F(0), F(1)), F(0)), (ZERO, F(1))):
    liquidation = tuple(-x for x in state[0])
    post = m3.review(state, liquidation)
    assert post[0] == ZERO and post[1] > 0
print(f'PASS: {mixtures} feasible policy mixtures across all nine controls')
print('PASS: exact cash/wealth concavity, strict positivity, bounds and control restrictions')
print('PASS: floating pathwise utility concavity; no general theorem or optimum asserted')
