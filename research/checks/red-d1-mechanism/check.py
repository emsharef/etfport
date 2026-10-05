"""Red's attack on the central mechanism (D1, M0 notation): three minimal cases in which an active trade
looks preferable only because of a hidden assumption. Backs the 2026-09-27 red entry in board/FINDINGS.md.

Everything is exact rational arithmetic. Each optimum is the unique KKT point of a strictly concave
quadratic program with linear constraints (Sigma positive definite), found by enumerating active sets;
for such a program a KKT point is the global maximizer, so every optimum below is certified, not an
incumbent. One quarter, excess returns (cash earns zero excess return), zero switching costs unless
stated, wealth before trading normalized to 1. All parameter values are assumed and illustrative.
"""
from itertools import combinations

from sympy import Matrix, Rational as R, zeros


def qp(mu, S, gamma, eq, ineq):
    """max mu'w - gamma/2 w'Sw  s.t.  r'w = b for (r, b) in eq,  r'w <= b for (r, b) in ineq."""
    n = len(mu)
    for k in range(len(ineq) + 1):
        for act in combinations(range(len(ineq)), k):
            rows = [r for r, _ in eq] + [ineq[i][0] for i in act]
            rhs = [b for _, b in eq] + [ineq[i][1] for i in act]
            m = len(rows)
            K = zeros(n + m, n + m)
            K[:n, :n] = gamma * S
            for j, r in enumerate(rows):
                for i in range(n):
                    K[i, n + j] = K[n + j, i] = r[i]
            if K.rank() < n + m:
                continue
            sol = K.LUsolve(Matrix(list(mu) + rhs))
            w, nu = sol[:n, 0], sol[n:, 0]
            if any(nu[len(eq) + j] < 0 for j in range(len(act))):
                continue  # dual infeasible
            if any(sum(r[i] * w[i] for i in range(n)) > b for r, b in ineq):
                continue  # primal infeasible
            val = (Matrix(mu).T * w)[0] - gamma / 2 * (w.T * S * w)[0]
            return list(w), val, list(nu)
    raise RuntimeError("no KKT point")


def unit(n, i, s=1):
    return [s if j == i else 0 for j in range(n)]


def fmt(v):
    return "(" + ", ".join(str(x) for x in v) + ")"


# Shared economy: K = 2 factors (1 = market, 2 = a style factor), quarterly.
Sf = Matrix.diag(R(4, 625), R(1, 625))   # factor variances: 8% and 4% quarterly volatility
s2e = R(1, 2500)                          # active-fund residual variance: 2% quarterly volatility


def economy(BA, BEs, lam, alpha, cE):
    B = Matrix([BA] + BEs)
    S = B * Sf * B.T + Matrix.diag(s2e, *([0] * len(BEs)))
    mu = [(Matrix([BA]) * lam)[0] + alpha] + [(Matrix([b]) * lam)[0] - cE for b in BEs]
    return mu, S


# ---------------------------------------------------------------- Case 1: hidden financing
# A = (1, 1/2), E = (1, 0); lambda = (3/200, 1/1000); alpha = 0; c^E = 0; gamma = 5/4.
# Pre-trade holdings a- = 1/2, p- = 1/2, h- = 0: the funded full-trading optimum (verified below).
lam = Matrix([R(3, 200), R(1, 1000)])
mu, S = economy([1, R(1, 2)], [[1, 0]], lam, 0, 0)
g = R(5, 4)
nonneg = [(unit(2, 0, -1), 0), (unit(2, 1, -1), 0)]
budget = [([1, 1], 1)]
fix_a = [(unit(2, 0), R(1, 2))]

full_f, V_full_f, nu_f = qp(mu, S, g, [], nonneg + budget)
etf_f, V_etf_f, _ = qp(mu, S, g, fix_a, nonneg + budget)
full_u, V_full_u, _ = qp(mu, S, g, [], nonneg)
etf_u, V_etf_u, _ = qp(mu, S, g, fix_a, nonneg)

assert full_f == [R(1, 2), R(1, 2)] and etf_f == full_f       # funded: no trade is optimal
assert V_full_f - V_etf_f == 0                                  # funded advantage exactly 0
budget_mult = nu_f[-1]                                          # multiplier on 1'w <= 1
w = Matrix(full_f)
grad = [mu[i] - g * (S * w)[i] for i in range(2)]               # unfunded marginal values at w
assert grad[0] == grad[1] == budget_mult == R(7, 1000)          # unfunded: buying A worth 0.7%/qtr
assert full_u == [R(1, 2), R(11, 8)] and etf_u == full_u        # unfunded optimum levers the ETF only
assert V_full_u - V_etf_u == 0                                  # so both-unfunded advantage is 0
assert V_full_u - V_etf_f == R(49, 16000)                       # mixed: 0.31%/qtr credited to full trading
print("Case 1a (financing)")
print("  funded   full", fmt(full_f), "ETF-only", fmt(etf_f), "advantage", V_full_f - V_etf_f)
print("  budget multiplier nu =", budget_mult, "= unfunded marginal value of buying A at the funded optimum")
print("  unfunded full", fmt(full_u), "sum", sum(full_u), "ETF-only", fmt(etf_u), "sum", sum(etf_u))
print("  unfunded advantage (both classes unfunded)", V_full_u - V_etf_u)
print("  mixed advantage (full unfunded, ETF-only funded)", V_full_u - V_etf_f, "=", float(V_full_u - V_etf_f))

# Relabelling check (M0 identity): attribute the style exposure to alpha against a market-only model.
# alpha' = alpha + (1/2) lambda_2, residual variance s2e' = s2e + (1/4) Var f_2. Same mu, same Sigma.
mu_r = [lam[0] + R(1, 2) * lam[1], lam[0]]
S_r = Matrix([[1], [1]]) * Matrix([[Sf[0, 0]]]) * Matrix([[1, 1]]) + Matrix.diag(s2e + R(1, 4) * Sf[1, 1], 0)
assert mu_r == mu and S_r == S
print("  relabelled (market-only model): mu and Sigma identical, so every optimum above is unchanged")

# Case 1b: same, but the ETF has a negative style loading, E = (1, -2/5); lambda_2 = 0 and alpha = 0, so
# A has no skill and its style exposure earns no premium. Pre-trade holdings = the funded optimum.
lam1b = Matrix([R(3, 200), 0])
mu1b, S1b = economy([1, R(1, 2)], [[1, R(-2, 5)]], lam1b, 0, 0)
full_f, V_full_f, _ = qp(mu1b, S1b, g, [], nonneg + budget)
assert full_f == [R(18, 53), R(35, 53)]
fix_a = [(unit(2, 0), full_f[0])]
etf_f, V_etf_f, _ = qp(mu1b, S1b, g, fix_a, nonneg + budget)
full_u, V_full_u, _ = qp(mu1b, S1b, g, [], nonneg)
etf_u, V_etf_u, _ = qp(mu1b, S1b, g, fix_a, nonneg)
assert etf_f == full_f and V_full_f == V_etf_f                  # funded: no trade, advantage 0
assert full_u[0] > full_f[0] and sum(full_u) > 1                # unfunded: buys zero-alpha A, levered
assert V_full_u - V_etf_u > 0
print("Case 1b (financing, style-hedging ETF)")
print("  funded   full", fmt(full_f), "advantage", V_full_f - V_etf_f)
print("  unfunded full", fmt(full_u), "sum", sum(full_u), "ETF-only", fmt(etf_u))
print("  active purchase", full_u[0] - full_f[0], "=", float(full_u[0] - full_f[0]),
      "; both-unfunded advantage", V_full_u - V_etf_u, "=", float(V_full_u - V_etf_u))

# ---------------------------------------------------------------- Case 2: hidden replication
# A = (1, 1/2), E1 = (1, 0), E2 = (1, 2/5). The ETF loadings span R^2, so A's exposure is algebraically
# matchable: (1, 1/2) = -1/4 E1 + 5/4 E2, but only with a short E1 position. Buying A at fixed exposure
# means selling 5/4 of E2 (and buying 1/4 of E1) per unit of A; the investor holds no E2.
# lambda = (3/200, 0); alpha = 3/5000 (6bp/qtr); c^E = 0; gamma = 2. Pre-trade a- = 1/2, p- = (1/2, 0), h- = 0.
lam = Matrix([R(3, 200), 0])
alpha = R(3, 5000)
mu, S = economy([1, R(1, 2)], [[1, 0], [1, R(2, 5)]], lam, alpha, 0)
g = R(2)
assert Matrix([[1, 1], [0, R(2, 5)]]).LUsolve(Matrix([1, R(1, 2)])) == Matrix([R(-1, 4), R(5, 4)])
nonneg_all = [(unit(3, i, -1), 0) for i in range(3)]
budget = [([1, 1, 1], 1)]
fix_a = [(unit(3, 0), R(1, 2))]

full_f, V_full_f, _ = qp(mu, S, g, [], nonneg_all + budget)
etf_f, V_etf_f, _ = qp(mu, S, g, fix_a, nonneg_all + budget)
# Replication allowed: ETF positions may be negative; budget and a >= 0 kept (no borrowing: every
# instrument has market loading 1, so market exposure = 1 - h <= 1 still).
full_r, V_full_r, _ = qp(mu, S, g, [], [nonneg_all[0]] + budget)
etf_r, V_etf_r, _ = qp(mu, S, g, fix_a, budget)

assert etf_f == [R(1, 2), R(1, 2), 0]                           # funded ETF-only: no trade
assert full_f == [R(3, 8), R(5, 8), 0]                          # funded full: SELL 1/8 of A
assert full_r[0] == R(3, 4) and full_r[2] < 0                   # replication: BUY 1/4 of A, short E2
assert full_r[0] == alpha / (g * s2e)                           # = alpha / (gamma s2e): residual-only rule
assert V_full_f - V_etf_f == R(1, 80000) and V_full_r - V_etf_r == R(1, 40000)
print("Case 2 (replication)")
print("  funded long-only full", fmt(full_f), "ETF-only", fmt(etf_f), "advantage", V_full_f - V_etf_f)
print("  with ETF shorting    full", fmt(full_r), "ETF-only", fmt(etf_r), "advantage", V_full_r - V_etf_r)
print("  active trade: funded", full_f[0] - R(1, 2), "(sell), with shorting", full_r[0] - R(1, 2), "(buy)")

# ---------------------------------------------------------------- Case 3: double-counted ETF drag
# Exact replication benchmark: A = E = (1, 0). alpha = -3/20000 (-1.5bp/qtr, net of fund costs),
# c^E = 1/10000 (1bp/qtr). Pre-trade a- = 0, p- = 1, h- = 0; gamma = 5/4.
lam = Matrix([R(3, 200), 0])
alpha, cE = R(-3, 20000), R(1, 10000)
g = R(5, 4)
nonneg = [(unit(2, 0, -1), 0), (unit(2, 1, -1), 0)]
budget = [([1, 1], 1)]
fix_a = [(unit(2, 0), 0)]
for label, drag in (("counted once", cE), ("counted twice", 2 * cE)):
    mu, S = economy([1, 0], [[1, 0]], lam, alpha, drag)
    full, Vf, _ = qp(mu, S, g, [], nonneg + budget)
    etf, Ve, _ = qp(mu, S, g, fix_a, nonneg + budget)
    print(f"Case 3 (ETF drag {label}): full", fmt(full), "ETF-only", fmt(etf), "advantage", Vf - Ve)
    if drag == cE:
        assert full == [0, 1] and Vf - Ve == 0                  # correct: stay in the ETF
    else:
        assert full[0] == (alpha + 2 * cE) / (g * s2e) == R(1, 10) and Vf - Ve > 0   # false buy
print("all assertions hold")
