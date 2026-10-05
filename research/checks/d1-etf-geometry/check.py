"""Exact, finite M2 exposure-feasibility checks; not a general proof.

Run: uv run python checks/d1-etf-geometry/check.py
All inputs are assumed. Complete each funding example to M2 with one parameter
point, one zero-shock scenario, zero means/drag and gamma = 0: gross returns = 1.
No economic advantage, calibration or optimizer comparison is tested.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, product


def vec(*xs):
    return tuple(F(x) for x in xs)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def solve(rows, rhs, n):
    """Exact elimination: consistency and one solution, with free entries zero."""
    a = [list(row) + [b] for row, b in zip(rows, rhs)]
    pivots = []
    r = 0
    for j in range(n):
        pivot = next((i for i in range(r, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        scale = a[r][j]
        a[r] = [v / scale for v in a[r]]
        for i in range(len(a)):
            if i != r:
                scale = a[i][j]
                a[i] = [x - scale * y for x, y in zip(a[i], a[r])]
        pivots.append(j)
        r += 1
    if any(not any(row[:n]) and row[n] for row in a):
        return None, len(pivots)
    x = [F(0)] * n
    for i, j in enumerate(pivots):
        x[j] = a[i][n]
    return tuple(x), len(pivots)


def feasible_vertex(eq, target, inequalities, bounds, n):
    """Enumerate vertices of a bounded box intersected with affine constraints."""
    rows = list(eq) + list(inequalities)
    rhs = list(target) + list(bounds)
    for active in combinations(range(len(rows)), n):
        x, rank = solve([rows[i] for i in active], [rhs[i] for i in active], n)
        if x is not None and rank == n:
            if all(dot(a, x) == b for a, b in zip(eq, target)) and all(
                dot(a, x) <= b for a, b in zip(inequalities, bounds)
            ):
                return x
    return None


@dataclass(frozen=True)
class Case:
    name: str
    active_loading: tuple
    etf_loadings: tuple
    initial: tuple
    full: tuple
    limits: tuple
    buy: tuple
    sell: tuple
    expected: str


def cash(case, holding):
    trades = tuple(w - old for w, old in zip(holding, case.initial))
    cost = sum(kp * max(v, 0) + km * max(-v, 0)
               for v, kp, km in zip(trades, case.buy, case.sell))
    return 1 - sum(case.initial) - sum(trades) - cost


def check(case):
    n = len(case.etf_loadings)
    assert all(0 <= x <= cap <= 1 for x, cap in zip(case.initial, case.limits))
    assert sum(case.initial) <= 1
    assert all(0 <= rate < 1 for rate in case.buy + case.sell)
    assert all(0 <= x <= cap for x, cap in zip(case.full, case.limits))
    assert cash(case, case.full) >= 0, case.name
    eq = tuple(tuple(row[j] for row in case.etf_loadings) for j in range(2))
    change = tuple(w - old for w, old in zip(case.full, case.initial))
    target = tuple(case.active_loading[j] * change[0] + dot(eq[j], change[1:])
                   for j in range(2))
    in_span, _ = solve(eq, target, n)
    box, bounds = [], []
    for j in range(n):
        for sign, bound in ((1, case.limits[j + 1] - case.initial[j + 1]),
                            (-1, case.initial[j + 1])):
            box.append(tuple(F(sign if i == j else 0) for i in range(n)))
            bounds.append(bound)
    # Candidate cash representation: all purchase/sale linear inequalities.
    budget = [tuple(1 + case.buy[j + 1] if s else 1 - case.sell[j + 1]
                    for j, s in enumerate(signs)) for signs in product((0, 1), repeat=n)]
    initial_cash = 1 - sum(case.initial)
    box_match = feasible_vertex(eq, target, box, bounds, n)
    funded_match = feasible_vertex(eq, target, box + budget,
                                   bounds + [initial_cash] * len(budget), n)
    category = ("missing direction" if in_span is None else
                "position bounds" if box_match is None else
                "funding" if funded_match is None else "feasible matching")
    assert category == case.expected, (case.name, category)
    if funded_match is not None:
        holding = (case.initial[0],) + tuple(old + d for old, d in
                                                        zip(case.initial[1:], funded_match))
        assert cash(case, holding) >= 0
        assert all(0 <= x <= cap for x, cap in zip(holding, case.limits))
        assert all(dot(row, funded_match) == b for row, b in zip(eq, target))
    # Compare the candidate budget representation with M2's direct cash formula,
    # including zero trades and both directions, on a fixed exact grid.
    for trade in product(vec('-1/2', '-1/4', 0, '1/4', '1/2'), repeat=n):
        holding = (case.initial[0],) + tuple(old + d for old, d in zip(case.initial[1:], trade))
        assert cash(case, holding) == initial_cash - max(dot(row, trade) for row in budget)
    print(f"{case.name}: {category}; ETF trade witness={funded_match}")


def main():
    one = (vec(1, 0),)
    identity = (vec(1, 0), vec(0, 1))
    zero2, zero3 = vec(0, 0), vec(0, 0, 0)
    cases = [
        Case("outside span", vec(0, 1), one, zero2, vec('1/4', 0), vec(1, 1), zero2, zero2, "missing direction"),
        Case("single ETF match", vec(1, 0), one, zero2, vec('1/4', 0), vec(1, 1), zero2, zero2, "feasible matching"),
        Case("shorting required", vec(1, '1/2'), (vec(1, 0), vec(1, '2/5')), zero3, vec('1/4', 0, 0), vec(1, 1, 1), zero3, zero3, "position bounds"),
        Case("borrowing required", vec(1, 1), identity, zero3, vec('3/4', 0, 0), vec(1, 1, 1), zero3, zero3, "funding"),
        Case("purchase costs block", vec(1, 1), identity, zero3, vec('1/2', 0, 0), vec(1, 1, 1), vec(0, '1/10', '1/10'), zero3, "funding"),
        Case("position cap blocks", vec(1, 0), identity, zero3, vec('1/2', 0, 0), vec(1, '1/4', 1), zero3, zero3, "position bounds"),
        Case("sale proceeds fund purchase", vec(0, 1), identity, vec(0, '1/2', 0), vec('1/2', '1/4', 0), vec(1, 1, 1), vec(0, 0, '1/4'), vec(0, '1/5', 0), "feasible matching"),
        Case("alternative redundant ETF", vec(1, 0), (vec(1, 0), vec(1, 0)), zero3, vec('1/2', 0, 0), vec(1, 0, 1), zero3, zero3, "feasible matching"),
    ]
    for case in cases:
        check(case)
    print("All fixed exact M2 checks passed. These checks are not a proof.")


if __name__ == "__main__":
    main()
