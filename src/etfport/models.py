"""Validated inputs for the finite, funded allocation problems."""
from dataclasses import dataclass
import numpy as np


def vector(value, name, n=None, *, nonnegative=False):
    a = np.array(value, dtype=float, copy=True)
    if a.ndim != 1 or (n is not None and a.size != n) or a.size == 0 or not np.isfinite(a).all():
        raise ValueError(f"{name} must be a finite vector" + (f" of length {n}" if n else ""))
    if nonnegative and np.any(a < 0):
        raise ValueError(f"{name} must be nonnegative")
    a.setflags(write=False)
    return a


def covariance(value, name, n, *, positive=False):
    a = np.array(value, dtype=float, copy=True)
    if a.shape != (n, n) or not np.isfinite(a).all() or not np.allclose(a, a.T, rtol=0, atol=1e-12):
        raise ValueError(f"{name} must be a finite symmetric {n} by {n} matrix")
    eigen = np.linalg.eigvalsh(a)
    if eigen.min() < -1e-12 or (positive and eigen.min() <= 0):
        raise ValueError(f"{name} must be positive {'definite' if positive else 'semidefinite'}")
    a.setflags(write=False)
    return a


@dataclass(frozen=True)
class Moments:
    """Quarterly excess means and predictive covariance in instrument order."""
    mean: np.ndarray
    covariance: np.ndarray

    def __post_init__(self):
        mean = vector(self.mean, 'mean')
        object.__setattr__(self, 'mean', mean)
        object.__setattr__(self, 'covariance', covariance(self.covariance, 'covariance', len(mean), positive=True))


@dataclass(frozen=True)
class TradingCosts:
    """Investor purchase/sale rates as decimals, not basis points."""
    buy: np.ndarray
    sell: np.ndarray

    def __post_init__(self):
        buy = vector(self.buy, 'buy rates', nonnegative=True)
        sell = vector(self.sell, 'sell rates', len(buy), nonnegative=True)
        if np.any(buy >= 1) or np.any(sell >= 1):
            raise ValueError('Trading rates must be less than one')
        object.__setattr__(self, 'buy', buy)
        object.__setattr__(self, 'sell', sell)

    def amount(self, trade):
        trade = vector(trade, 'trade', len(self.buy))
        return float(self.buy @ np.maximum(trade, 0) + self.sell @ np.maximum(-trade, 0))


@dataclass(frozen=True)
class Portfolio:
    """Pre-review dollar holdings and nonnegative cash, in a fixed wealth unit."""
    holdings: np.ndarray
    cash: float

    def __post_init__(self):
        object.__setattr__(self, 'holdings', vector(self.holdings, 'holdings', nonnegative=True))
        if not np.isfinite(self.cash) or self.cash < 0:
            raise ValueError('Cash must be finite and nonnegative')
        if self.wealth <= 0:
            raise ValueError('Initial wealth must be positive')

    @property
    def wealth(self):
        return float(self.holdings.sum() + self.cash)


@dataclass(frozen=True)
class Scenario:
    """One observed next-review state, with its conditional score moments.

    Supply one node per observable information state. Hidden outcomes that the
    manager cannot distinguish must not receive distinct decisions.
    """
    probability: float
    gross_returns: np.ndarray
    moments: Moments
    label: str = ''

    def __post_init__(self):
        if not np.isfinite(self.probability) or self.probability <= 0:
            raise ValueError('Scenario probability must be finite and strictly positive')
        g = vector(self.gross_returns, 'gross returns', len(self.moments.mean))
        if np.any(g <= 0):
            raise ValueError('Gross returns must be strictly positive')
        object.__setattr__(self, 'gross_returns', g)


@dataclass(frozen=True)
class AllocationProblem:
    """A fully funded one-review problem, optionally with one future review.

    All positions are dollars, caps are dollar caps, and gamma multiplies a
    dollar-quadratic score. Changing the wealth unit requires rescaling gamma.
    """
    moments: Moments
    portfolio: Portfolio
    costs: TradingCosts
    gamma: float
    names: tuple[str, ...] = ()
    fund_indices: tuple[int, ...] = ()
    caps: np.ndarray | None = None
    scenarios: tuple[Scenario, ...] = ()
    discount: float = 1.0

    def __post_init__(self):
        n = len(self.moments.mean)
        if len(self.portfolio.holdings) != n or len(self.costs.buy) != n:
            raise ValueError('Moments, portfolio and costs must have the same dimension')
        if not np.isfinite(self.gamma) or self.gamma <= 0:
            raise ValueError('gamma must be finite and strictly positive')
        if not np.isfinite(self.discount) or not 0 < self.discount <= 1:
            raise ValueError('discount must lie in (0, 1]')
        names = tuple(self.names) or tuple(f'Asset {i}' for i in range(n))
        if len(names) != n or len(set(names)) != n or any(not isinstance(x, str) or not x for x in names):
            raise ValueError('Instrument names must be nonempty, unique, and match the dimension')
        funds = tuple(self.fund_indices)
        if len(set(funds)) != len(funds) or any(not isinstance(i, (int, np.integer)) or i < 0 or i >= n for i in funds):
            raise ValueError('Fund indices must be distinct valid integer indices')
        caps = np.full(n, np.inf) if self.caps is None else np.array(self.caps, dtype=float, copy=True)
        if caps.shape != (n,) or np.isnan(caps).any() or np.any(caps < 0):
            raise ValueError('Caps must be nonnegative dollar amounts or positive infinity')
        caps.setflags(write=False)
        scenarios = tuple(self.scenarios)
        if scenarios:
            if any(len(z.gross_returns) != n for z in scenarios):
                raise ValueError('Every scenario must have the same instrument dimension')
            if not np.isclose(sum(z.probability for z in scenarios), 1, atol=1e-12, rtol=0):
                raise ValueError('Scenario probabilities must sum to one')
        for key, value in [('names',names),('fund_indices',funds),('caps',caps),('scenarios',scenarios)]:
            object.__setattr__(self, key, value)
