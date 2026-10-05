"""Exact finite checks for claim 015, not its arbitrary-law rate proof.

Run: uv run python checks/015/check.py
Checks funded costs/caps, actual full-observation likelihoods, finite affinities,
and a conservative certificate over all 513 count classes of a 512-record law.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import comb, factorial

import sympy as sp


KA, KE, MU, DLOAD, H = F(1, 10), F(1, 50), F(1, 10), F(2), F(1, 20)
EPS = F(1, 16)


def geometry(cap):
    a = min(cap, 1 / (1 + KA))
    q = (MU - KE) / (1 + KE)
    center = (KA + (1 + KA) * q) / DLOAD
    active = (a, (1 - (1 + KA)*a) / (1 + KE))
    etf = (F(0), 1 / (1 + KE))
    return a, DLOAD*a, q, center, active, etf


def score(w, lam):
    a, p = w
    return a * DLOAD * lam + p * MU - KA*a - KE*p


def check_geometry():
    a, d, ka, ke, mu, lam = sp.symbols('a d ka ke mu lam')
    qe = (mu-ke)/(1+ke)
    center = (ka+(1+ka)*qe)/d
    p = (1-(1+ka)*a)/(1+ke)
    q = a*d*lam+p*mu-ka*a-ke*p
    assert sp.factor(q-qe-a*d*(lam-center)) == 0
    assert sp.factor((1+ka)*a+(1+ke)*p-1) == 0
    for cap in (F(1, 2), F(1)):
        capacity, mismatch, qe, center, active, etf = geometry(cap)
        assert capacity == (cap if cap == F(1, 2) else 1/(1+KA))
        corners = [(0, 0), etf, (capacity, 0), active]
        for w in corners:
            assert 0 <= w[0] <= cap and 0 <= w[1] <= 1
            assert (1+KA)*w[0]+(1+KE)*w[1] <= 1
        for lam in (center-H, center, center+H):
            optimum = max(score(w, lam) for w in corners)
            assert optimum-qe == mismatch*max(lam-center, 0)
            assert score(active, lam)-qe == mismatch*(lam-center)
            for shock in (-H, H):
                assert 1+DLOAD*(lam+shock) > 0 and 1+MU > 0
        assert score(etf, center) == qe


def full_record_law(noises, weights, lam):
    out = defaultdict(F)
    for noise, mass in zip(noises, weights):
        x = lam + noise
        # Actual public data, not a hidden shock index: f1, f2, rA, rE.
        out[(x, MU, DLOAD*x, MU)] += mass
    return dict(out)


def history_law(atoms, count):
    out = {(): F(1)}
    for _ in range(count):
        new = defaultdict(F)
        for hist, p in out.items():
            for obs, q in atoms.items():
                new[hist+(obs,)] += p*q
        out = dict(new)
    return out


def endpoint_power(null, alt, budget):
    power = sum(q for x, q in alt.items() if not null.get(x, 0))
    ranked = sorted(((q/null[x], null[x], q) for x, q in alt.items()
                     if null.get(x, 0)), reverse=True)
    for _, cost, benefit in ranked:
        take = min(F(1), budget/cost)
        budget -= take*cost
        power += take*benefit
    return power


def check_hard_laws():
    _, mismatch, _, center, _, _ = geometry(F(1, 2))
    for m in (3, 5):
        spacing_half = H/(m-1)
        delta = mismatch*spacing_half
        assert 0 < delta <= mismatch*H/2
        phi = sp.pi/(m+1)
        u = [sp.sin(i*phi) for i in range(1, m+1)]
        normalizer = sp.simplify(sum(x*x for x in u))
        symbolic_weights = [sp.simplify(x*x/normalizer) for x in u]
        assert all(q.is_Rational for q in symbolic_weights)
        weights = [F(int(q.p), int(q.q)) for q in symbolic_weights]
        noises = [2*spacing_half*(F(i)-F(m+1, 2)) for i in range(1, m+1)]
        assert sum(weights) == 1 and min(weights) > 0
        assert sum(q*z for q, z in zip(weights, noises)) == 0
        assert max(abs(z) for z in noises) <= H
        neg = full_record_law(noises, weights, center-spacing_half)
        pos = full_record_law(noises, weights, center+spacing_half)
        for count in (1, 2):
            p, q = history_law(neg, count), history_law(pos, count)
            keys = set(p) | set(q)
            affinity = sp.simplify(sum(sp.sqrt(sp.Rational(p.get(x, 0)*q.get(x, 0))) for x in keys))
            assert sp.simplify(affinity-sp.cos(phi)**count) == 0
            tv = sum(abs(p.get(x, 0)-q.get(x, 0)) for x in keys)/2
            assert sp.simplify(1-affinity**2-sp.Rational(tv)**2) >= 0
            optimum = endpoint_power(p, q, EPS)
            # If the affinity condition rules out two errors <= EPS, so must
            # the independently optimized endpoint test on full records.
            if sp.simplify(affinity**2) > 4*EPS*(1-EPS):
                assert optimum < 1-EPS
    print('Exact hard-law checks passed: full-record affinities for m=3,5 and N_obs=1,2.')


def check_conservative_gate():
    count = 512
    _, mismatch, qe, center, active, etf = geometry(F(1, 2))
    delta = mismatch*H/2
    # exp(4)>32, established by a finite positive partial sum. Hence log(32)<4,
    # N=512 >= 32*(D H/delta)^2*log(2/EPS), and r_B < H/8.
    assert sum(F(4**k, factorial(k)) for k in range(6)) > 32
    assert count == 32*(mismatch*H/delta)**2*4
    radius_bound = H/8
    errors = {H*F(2*k-count, count): F(comb(count, k), 2**count)
              for k in range(count+1)}
    statistics = defaultdict(F)
    for error, mass in errors.items():
        statistics[count*error**2/H**2] += mass
    cumulative = F(0)
    for critical in sorted(statistics):
        cumulative += statistics[critical]
        if cumulative >= 1-EPS:
            break
    radius = max(abs(e) for e in errors if count*e**2/H**2 <= critical)
    assert radius <= radius_bound and cumulative >= 1-EPS
    for lam in (center-H, center, center+delta/(4*mismatch),
                center+delta/mismatch, center+H):
        false = correct = coverage = F(0)
        for error, mass in errors.items():
            estimate = lam+error
            lo = max(center-H, estimate-radius)
            hi = min(center+H, estimate+radius)
            nonempty = lo <= hi
            candidate = active if estimate > center else etf
            lower = mismatch*(estimate-radius_bound-center)
            certify = nonempty and candidate == active and lower > delta/4
            advantage = score(candidate, lam)-qe
            covered = lo <= lam <= hi
            if nonempty:
                assert lower <= score(active, lo)-qe
            if covered and mismatch*max(lam-center, 0) >= delta:
                assert candidate == active and lower >= delta/2 and certify
            coverage += mass*covered
            false += mass*(certify and advantage <= delta/4)
            correct += mass*(certify and advantage > delta/4)
        assert coverage == cumulative and false <= EPS
        if mismatch*max(lam-center, 0) >= delta:
            assert correct >= 1-EPS
    print('Exact 512-record gate check passed: positive costs, binding active cap, all binomial count classes.')


if __name__ == '__main__':
    check_geometry()
    check_hard_laws()
    check_conservative_gate()
    print('Claim 015 finite checks passed; the general rate and class quantifiers require the paper proof.')
