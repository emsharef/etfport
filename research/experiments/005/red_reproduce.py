"""Red's independent reproduction of experiment 005.

1. Runs the registered harness unchanged (run.t1, run.t2, run.t3 with seed 2005, in run.main's order),
   recording every exact solver call and every T3 instance drawn.
2. Certifies every exact solver result with red's own exact KKT certificate: red's own mean vector,
   Sigma (scenario enumeration), objective, feasibility and the directional subdifferential, as in
   red's reproduction of experiment 004. A certificate proves global optimality; with Sigma positive
   definite and gamma > 0 (every instance here) the optimizer is unique, so a* is certified.
3. Recomputes every T3 band exactly, without bisection. With all data but alpha fixed, a*(alpha) = a0
   iff the ETF-only optimum w_E is optimal on F. w_E does not depend on alpha, since with a = a0 alpha
   only adds a constant. By the KKT certificate that holds iff the active coordinate's condition is met
   by some budget multiplier eta_B in the range [lo, hi] that the ETF coordinates allow at w_E. With
   g_A(alpha) = mu_A - gamma (Sigma w_E)_A, which is alpha plus a constant, and 0 < a0 < 1 = wbar_A,
       band in g_A = [(1 - kappa^-_A) lo - kappa^-_A,  (1 + kappa^+_A) hi + kappa^+_A],
       width = kappa^+_A (1 + hi) + kappa^-_A (1 + lo) + (hi - lo).
   (Corrected 2026-09-27 after math's note: an earlier header printed 1 - lo in the sale term. The code
   below always subtracted the endpoints above, so no computed number changes.)
   If lo = hi = 0 the width is kappa^+_A + kappa^-_A, costs alone. A slack budget forces this, but a
   tight budget can also have a zero multiplier. An ETF traded off its kink and strictly inside its
   position bounds pins lo = hi = eta_B, and the width is then (kappa^+_A + kappa^-_A)(1 + eta_B), which
   moves with anything that moves eta_B, lam_2 included.

Usage: uv run python experiments/005/red_reproduce.py
"""
import itertools
import sys
from collections import defaultdict
from dataclasses import replace
from fractions import Fraction as Fr
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run  # noqa: E402  (registered harness; its solver is the object under test)

EXACT, T3_DRAWS = [], []
_solve, _draw = run.solve, run.draw


def recording_solve(I, cls, exact=False):
    out = _solve(I, cls, exact=exact)
    if exact:
        EXACT.append((I, cls, out))
    return out


def recording_draw(rng, n, **kw):
    out = _draw(rng, n, **kw)
    if kw.get("interior_active"):
        T3_DRAWS.append(out)
    return out


run.solve, run.draw = recording_solve, recording_draw


# ---------------------------------------------------------------- red's own M2 objects
def red_model(I):
    n = len(I.BE)
    B = [I.BA] + list(I.BE)
    mu = [I.BA[0] * I.lam[0] + I.BA[1] * I.lam[1] + I.alpha] + \
         [b[0] * I.lam[0] + b[1] * I.lam[1] - c for b, c in zip(I.BE, I.cE)]
    sizes = list(I.sf) + [I.sA] + list(I.sE)
    scen = list(itertools.product((-1, 1), repeat=len(sizes)))
    q, d = Fr(1, len(scen)), 1 + n
    Sig = [[Fr(0)] * d for _ in range(d)]
    ok = True
    for sg in scen:
        z = [s * x for s, x in zip(sg, sizes)]
        xi = [B[i][0] * z[0] + B[i][1] * z[1] + z[2 + i] for i in range(d)]
        for i in range(d):
            for j in range(d):
                Sig[i][j] += q * xi[i] * xi[j]
            ok = ok and 1 + mu[i] + xi[i] > 0
    return mu, Sig, ok


def cost(I, w):
    return sum(I.kbuy[i] * max(w[i] - I.w0[i], 0) + I.ksell[i] * max(I.w0[i] - w[i], 0) for i in range(len(w)))


def qbar(I, mu, Sig, w):
    d = len(w)
    return (sum(mu[i] * w[i] for i in range(d))
            - I.gamma / 2 * sum(w[i] * Sig[i][j] * w[j] for i in range(d) for j in range(d)) - cost(I, w))


def slack(I, w):
    return I.k0 - sum(w[i] - I.w0[i] for i in range(len(w))) - cost(I, w)


def feasible(I, w, cls):
    ok = all(0 <= w[i] <= I.wbar[i] for i in range(len(w))) and slack(I, w) >= 0
    return ok and (cls != "E" or w[0] == I.w0[0])


def eta_range(I, mu, Sig, w, skip):
    """Exact range [lo, hi] of budget multipliers compatible with the KKT conditions of the coordinates
    not in `skip` (hi None = unbounded above; lo > hi = no multiplier)."""
    d = len(w)
    g = [mu[i] - I.gamma * sum(Sig[i][j] * w[j] for j in range(d)) for i in range(d)]
    lo, hi = Fr(0), (None if slack(I, w) == 0 else Fr(0))
    for i in range(d):
        if i in skip:
            continue
        if w[i] > I.w0[i]:
            zmin = zmax = I.kbuy[i]
        elif w[i] < I.w0[i]:
            zmin = zmax = -I.ksell[i]
        else:
            zmin, zmax = -I.ksell[i], I.kbuy[i]
        if w[i] != 0:
            ub = (g[i] - zmin) / (1 + zmin)
            hi = ub if hi is None else min(hi, ub)
        if w[i] != I.wbar[i]:
            lo = max(lo, (g[i] - zmax) / (1 + zmax))
    return lo, hi, g


def certified(I, cls, w):
    mu, Sig, ok = red_model(I)
    w = list(w)
    lo, hi, _ = eta_range(I, mu, Sig, w, {0} if cls == "E" else set())
    return ok and feasible(I, w, cls) and (hi is None or lo <= hi)


def exact_band(I):
    """Exact alpha-band {alpha : a*(alpha) = a0} and its width, or None if unbounded."""
    wE = list(_solve(I, "E", exact=True)[1])
    assert certified(I, "E", wE), "ETF-only optimum not certified"
    mu, Sig, _ = red_model(I)
    lo, hi, g = eta_range(I, mu, Sig, wE, {0})
    if hi is None:
        return None
    kp, km = I.kbuy[0], I.ksell[0]
    gL, gU = (1 - km) * lo - km, (1 + kp) * hi + kp
    shift = g[0] - I.alpha                    # g_A(alpha) = alpha + shift
    return gL - shift, gU - shift, gU - gL, lo == hi


# ---------------------------------------------------------------- run the registered search
rng = np.random.default_rng(run.SEED)
s1, f1 = run.t1(rng)
s2, f2 = run.t2(rng)
n_before_t3 = len(EXACT)
s3, f3 = run.t3(rng)
print("harness T1:", dict(sorted(s1.items())))
print("harness T2:", dict(sorted(s2.items())))
print("harness T3:", dict(sorted(s3.items())))

bad = [i for i, (I, cls, (V, w, _)) in enumerate(EXACT)
       if not certified(I, cls, w) or qbar(I, *red_model(I)[:2], list(w)) != V]
print(f"exact solver results: {len(EXACT)}; certified with value check: {len(EXACT) - len(bad)}; failures: {len(bad)}")

# Reported examples, checked from the harness's own first-counterexample records.
for fam in sorted(f1):
    _, I2, a2, e1, e2, a1 = f1[fam]
    I1 = run.drop_second_etf(I2)
    w1, w2 = _solve(I1, "F", exact=True)[1], _solve(I2, "F", exact=True)[1]
    assert certified(I1, "F", w1) and certified(I2, "F", w2)
    a0 = I2.w0[0]
    print(f"T1 {fam}: a* one ETF {w1[0]}, two ETFs {w2[0]}, |change| {abs(w1[0]-a0)} -> {abs(w2[0]-a0)}",
          "VIOLATION" if abs(w2[0] - a0) > abs(w1[0] - a0) else "no violation")
if f2:
    fam, J0, J1, x0, x1 = f2
    w0_, w1_ = _solve(J0, "F", exact=True)[1], _solve(J1, "F", exact=True)[1]
    assert certified(J0, "F", w0_) and certified(J1, "F", w1_)
    print(f"T2 {fam}: a* {w0_[0]} at lam_2 {J0.lam[1]} -> {w1_[0]} at lam_2 {J1.lam[1]}",
          "VIOLATION" if w1_[0] < w0_[0] else "no violation")

# T3 exactly, on every drawn T3 instance, with the harness's inclusion rules.
tab = defaultdict(lambda: [0, 0, 0, 0])      # counted, widths differ, max |diff| (bp), pinned both
for fam, I in T3_DRAWS:
    Is = [replace(I, lam=(I.lam[0], l2)) for l2 in run.T3_LAM2]
    if any(run.check_instance(replace(J, alpha=x)) for J in Is for x in run.ALPHA_RANGE):
        continue
    bands = [exact_band(J) for J in Is]
    if any(b is None or not (run.ALPHA_RANGE[0] < b[0] and b[1] < run.ALPHA_RANGE[1]) for b in bands):
        continue
    t = tab[(fam, len(I.BE))]
    t[0] += 1
    diff = abs(bands[0][2] - bands[1][2])
    if diff != 0:
        t[1] += 1
        t[2] = max(t[2], float(diff) * 10000)
    t[3] += bands[0][3] and bands[1][3]
print("\nT3 exact: family, n: [instances with both bands inside, widths differ exactly, max |width diff| bp, eta_B pinned at both]")
for k in sorted(tab):
    print(" ", k, tab[k])


# ---------------------------------------------------------------- direct confirmation of exact T3 bands
def confirm(J, band_, e=Fr(1, 10 ** 12)):
    """The band is a closed interval (a* is monotone in alpha and continuous). Check a*(L - e) < a0,
    a*(L) = a0 = a*(U) and a*(U + e) > a0 at the exact rational endpoints, every point KKT-certified by
    red's code. Then the exact width lies in [U - L, U - L + 2e]."""
    L, U, W, _ = band_
    a0, out = J.w0[0], []
    for x in (L - e, L, U, U + e):
        K = replace(J, alpha=x)
        w = _solve(K, "F", exact=True)[1]
        assert certified(K, "F", w)
        out.append(w[0])
    return out[0] < a0 == out[1] == out[2] < out[3]


harness_band, harness_cert = run.band, run.certify_band
print("\nT3 exact counterexamples, each confirmed directly (exact solver at L - 1e-12, L, U, U + 1e-12, every point")
print("KKT-certified), with what the harness did: screened out (float |diff| <= 1e-6) or certification failed:")
summary = defaultdict(lambda: [0, 0, 0, 0, 0.0, None])   # ..., max bp, min bp
first = {}
for fam, I in T3_DRAWS:
    Is = [replace(I, lam=(I.lam[0], l2)) for l2 in run.T3_LAM2]
    if any(run.check_instance(replace(J, alpha=x)) for J in Is for x in run.ALPHA_RANGE):
        continue
    bands = [exact_band(J) for J in Is]
    if any(b is None or not (run.ALPHA_RANGE[0] < b[0] and b[1] < run.ALPHA_RANGE[1]) for b in bands):
        continue
    if bands[0][2] == bands[1][2]:
        continue
    t = summary[(fam, len(I.BE))]
    t[0] += 1
    t[1] += all(confirm(J, b) for J, b in zip(Is, bands))
    hb = [harness_band(J) for J in Is]
    if abs((hb[0][1] - hb[0][0]) - (hb[1][1] - hb[1][0])) <= 1e-6:
        t[2] += 1
    else:
        c = [harness_cert(J, *b) for J, b in zip(Is, hb)]
        t[3] += not (all(c) and (c[0][1] < c[1][0] or c[1][1] < c[0][0]))
    dbp = abs(float(bands[0][2] - bands[1][2])) * 1e4
    t[4] = max(t[4], dbp)
    t[5] = dbp if t[5] is None else min(t[5], dbp)
    if fam in ("EQ", "ETFC") and fam not in first:
        first[fam] = (Is[0], bands)
for k in sorted(summary):
    c, ok, scr, cf, mx, mn = summary[k]
    print(f"  {k}: {c} exact counterexamples, {ok} confirmed; harness: {scr} screened out, {cf} certification failed,"
          f" {c - scr - cf} certified; |width diff| {mn:.3g} to {mx:.4g} bp")
for fam, (J, bands) in first.items():
    print(f"\nFirst exact {fam} counterexample: {run.show(J)} (lam_2 varied over {list(run.T3_LAM2)}).")
    for l2, b in zip(run.T3_LAM2, bands):
        print(f"  lam_2 = {l2}: band [{b[0]}, {b[1]}]; width {b[2]} = {float(b[2]) * 1e4:.6f} bp")
