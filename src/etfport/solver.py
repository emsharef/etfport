"""Convex numerical solvers for the paper's funded quarterly score."""
from dataclasses import dataclass, asdict
import warnings
import cvxpy as cp
import numpy as np
from .models import AllocationProblem, vector

SCALE = 1e4


class SolverError(RuntimeError):
    """The solver failed or its output failed independent accounting checks."""


@dataclass(frozen=True)
class SolverOptions:
    absolute_tolerance: float = 1e-9
    relative_tolerance: float = 1e-10
    feasibility_tolerance: float = 1e-10
    max_iterations: int = 1000

    def __post_init__(self):
        if any(not np.isfinite(v) or v <= 0 for v in (self.absolute_tolerance,self.relative_tolerance,self.feasibility_tolerance)):
            raise ValueError('Solver tolerances must be finite and strictly positive')
        if not isinstance(self.max_iterations, int) or self.max_iterations < 1:
            raise ValueError('max_iterations must be a positive integer')


@dataclass
class Allocation:
    holdings: np.ndarray
    trades: np.ndarray
    cash: float
    transaction_cost: float
    score: float
    cash_multiplier: float | None


@dataclass
class PolicyResult:
    current: Allocation
    future: tuple[Allocation, ...]
    value: float
    future_probabilities: np.ndarray
    effective_cash_multiplier: float | None
    status: str
    solve_seconds: float
    warnings: tuple[str, ...]
    max_accounting_error: float

    def to_dict(self):
        def convert(obj):
            if isinstance(obj, np.ndarray): return obj.tolist()
            if isinstance(obj, dict): return {k:convert(v) for k,v in obj.items()}
            if isinstance(obj, (list,tuple)): return [convert(v) for v in obj]
            if isinstance(obj, np.generic): return obj.item()
            return obj
        return convert(asdict(self))


@dataclass
class PolicyComparison:
    etf_only: PolicyResult
    one_review: PolicyResult
    planning: PolicyResult
    current_fund_benefit_bp: float
    planning_gain_bp: float
    initial_wealth: float

    def to_dict(self):
        return dict(etf_only=self.etf_only.to_dict(),one_review=self.one_review.to_dict(),planning=self.planning.to_dict(),
                    current_fund_benefit_bp=self.current_fund_benefit_bp,planning_gain_bp=self.planning_gain_bp,
                    initial_wealth=self.initial_wealth,units='Score bp of initial wealth; costs already deducted; not realized returns')


def _solve(program, options):
    with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter('always')
        try:
            program.solve(solver='CLARABEL',tol_gap_abs=options.absolute_tolerance,tol_gap_rel=options.relative_tolerance,
                          tol_feas=options.feasibility_tolerance,max_iter=options.max_iterations)
        except cp.error.SolverError as exc:
            raise SolverError(str(exc)) from exc
    if program.status != cp.OPTIMAL:
        raise SolverError(f'Allocation solve did not reach optimal status: {program.status}')
    return tuple(str(w.message) for w in caught)


def _allocation(P, moments, x, incumbent, cash, multiplier):
    x = np.asarray(x,dtype=float).copy()
    u = x - incumbent
    cost = P.costs.amount(u)
    h = float(cash - u.sum() - cost)
    score = float(moments.mean@x - P.gamma/2*x@moments.covariance@x - cost)
    violation = max(0., -float(x.min()), -h, float(np.max(x-P.caps)))
    if violation > 2e-7*max(1,P.portfolio.wealth):
        raise SolverError(f'Computed policy violates funded holdings/cash constraints by {violation:g}')
    return Allocation(x,u,h,cost,score,multiplier)


def _root(P, frozen=()):
    n = len(P.moments.mean)
    x=cp.Variable(n);buy=cp.Variable(n,nonneg=True);sell=cp.Variable(n,nonneg=True)
    cost=P.costs.buy@buy+P.costs.sell@sell
    cash=P.portfolio.cash-cp.sum(x-P.portfolio.holdings)-cost
    budget=cash>=0
    cons=[x>=0,x-P.portfolio.holdings==buy-sell,budget]
    finite=np.flatnonzero(np.isfinite(P.caps))
    if len(finite): cons.append(x[finite]<=P.caps[finite])
    frozen=tuple(frozen)
    if any(not isinstance(i,(int,np.integer)) or i<0 or i>=n for i in frozen) or len(set(frozen))!=len(frozen):
        raise ValueError('Frozen indices must be distinct valid integer indices')
    if frozen:cons.append(x[list(frozen)]==P.portfolio.holdings[list(frozen)])
    score=P.moments.mean@x-P.gamma/2*cp.quad_form(x,cp.psd_wrap(P.moments.covariance))-cost
    return x,cash,score,budget,cons


def solve_one_review(P: AllocationProblem, *, frozen=(), options=SolverOptions()) -> PolicyResult:
    """Optimize only today's net score. Frozen instruments retain dollar holdings."""
    x,h,score,budget,cons=_root(P,frozen)
    program=cp.Problem(cp.Maximize(SCALE*score),cons)
    messages=_solve(program,options)
    result=_allocation(P,P.moments,x.value,P.portfolio.holdings,P.portfolio.cash,float(budget.dual_value)/SCALE)
    error=max(abs(result.score-program.value/SCALE),abs(result.cash-float(h.value)))
    if error>1e-7*max(1,P.portfolio.wealth):raise SolverError(f'Objective/cash reconstruction error: {error:g}')
    return PolicyResult(result,(),result.score,np.array([]),result.cash_multiplier,program.status,
                        float(program.solver_stats.solve_time or 0),messages,error)


def solve_two_review(P: AllocationProblem, *, first_holdings=None, options=SolverOptions()) -> PolicyResult:
    """Optimize today's allocation and one funded decision in each future state.

    first_holdings fixes today's action to evaluate a benchmark with optimal
    continuation. Its current/effective cash multipliers are then undefined.
    The horizon ends after the second score; no liquidation cost is imposed.
    """
    if not P.scenarios:raise ValueError('Two-review optimization requires future scenarios')
    x,h,current,budget,cons=_root(P)
    if first_holdings is not None:
        fixed=vector(first_holdings,'first_holdings',len(P.moments.mean))
        # Permit only solver-scale negative entries returned by another solve.
        if np.min(fixed)<-2e-7:raise ValueError('Fixed holdings cannot be negative')
        cons.append(x==fixed)
    n=len(P.moments.mean);z=len(P.scenarios)
    X=cp.Variable((n,z));buy=cp.Variable((n,z),nonneg=True);sell=cp.Variable((n,z),nonneg=True)
    q=np.array([a.probability for a in P.scenarios]);g=np.column_stack([a.gross_returns for a in P.scenarios])
    carried=cp.multiply(g,cp.reshape(x,(n,1),order='F'))
    costs=P.costs.buy@buy+P.costs.sell@sell
    future_cash=h-cp.sum(X-carried,axis=0)-costs
    future_budget=future_cash>=0
    cons += [X>=0,X-carried==buy-sell,future_budget]
    finite=np.flatnonzero(np.isfinite(P.caps))
    if len(finite):cons.append(X[finite,:]<=P.caps[finite,None])
    means=np.column_stack([a.moments.mean for a in P.scenarios])
    expected=cp.sum(cp.multiply(means,X)@q)-costs@q
    cov0=P.scenarios[0].moments.covariance
    if all(np.array_equal(a.moments.covariance,cov0) for a in P.scenarios):
        deviations=np.linalg.cholesky(cov0).T@X
        expected -= P.gamma/2*cp.sum(cp.multiply(q,cp.sum(cp.square(deviations),axis=0)))
    else:
        expected -= P.gamma/2*sum(q[j]*cp.quad_form(X[:,j],cp.psd_wrap(a.moments.covariance)) for j,a in enumerate(P.scenarios))
    program=cp.Problem(cp.Maximize(SCALE*(current+P.discount*expected)),cons)
    messages=_solve(program,options)
    eta0=None if first_holdings is not None else float(budget.dual_value)/SCALE
    eta1=np.asarray(future_budget.dual_value)/(SCALE*P.discount*q)
    root=_allocation(P,P.moments,x.value,P.portfolio.holdings,P.portfolio.cash,eta0)
    future=tuple(_allocation(P,a.moments,X.value[:,j],a.gross_returns*root.holdings,root.cash,float(eta1[j])) for j,a in enumerate(P.scenarios))
    value=root.score+P.discount*float(q@np.array([a.score for a in future]))
    error=max(abs(value-program.value/SCALE),abs(root.cash-float(h.value)),float(np.max(abs(np.array([a.cash for a in future])-future_cash.value))))
    if error>1e-7*max(1,P.portfolio.wealth):raise SolverError(f'Objective/cash reconstruction error: {error:g}')
    effective=None if eta0 is None else eta0+P.discount*float(q@eta1)
    return PolicyResult(root,future,value,q,effective,program.status,float(program.solver_stats.solve_time or 0),messages,error)


def compare_policies(P: AllocationProblem, *, options=SolverOptions()) -> PolicyComparison:
    """Compare ETF-only today, repeated one-review, and funded two-review planning.

    Every benchmark can trade all instruments next review. ETF-only is defined
    by fund_indices; the complement may contain any liquid instruments.
    """
    myopic=solve_one_review(P,options=options)
    etf=solve_one_review(P,frozen=P.fund_indices,options=options)
    plan=solve_two_review(P,options=options)
    my_future=solve_two_review(P,first_holdings=myopic.current.holdings,options=options)
    etf_future=solve_two_review(P,first_holdings=etf.current.holdings,options=options)
    # Keep the separately solved one-review multipliers; never report the
    # arbitrary root dual from a continuation solve with fixed holdings.
    my_future.current.cash_multiplier=myopic.current.cash_multiplier
    etf_future.current.cash_multiplier=etf.current.cash_multiplier
    W=P.portfolio.wealth
    return PolicyComparison(etf_future,my_future,plan,
        SCALE*(myopic.current.score-etf.current.score)/W,SCALE*(plan.value-my_future.value)/W,W)
