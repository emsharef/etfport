"""Named input sets for the formula checks (experiments 028-034) and the regime map (027): the human's item 1,
kept minimal by the scope-down note (2026-09-29). Every value is ASSUMED (AGENTS.md rules 19, 22); the ranges
experiment 035's survivor-only Yahoo pilot reports may later bound them, and each such change is recorded here
with its source. Units: per quarter; rates and fees as fractions of the amount traded or held.

Import: from experiments.presets import PRESETS, STARTS (or load by path from an experiment's run.py).
"""

SOURCE = "assumed (2026-09-29); no input estimated yet (experiment 035 will report survivor-only ranges)"

PRESETS = {
    # Mostly negative net alpha, cheap ETFs, a menu that spans the factors.
    "equity-style": dict(
        alpha_mean=-0.0019,          # mean net alpha of the fund population
        alpha_sd=0.0035,             # prior SD s (dispersion of true net alpha)
        alpha_persistence=1.0,       # phi (1 = fixed alpha)
        sigma_A=0.02,                # fund residual SD
        premium=(0.015, 0.005),      # lambda_hat, K = 2 factors
        premium_sd=(0.005, 0.005),   # sqrt(diag P^lambda)
        factor_sd=(0.08, 0.04),      # sqrt(diag Sigma_f)
        fund_rate=0.0050,            # proportional kappa^+ = kappa^- (M7 checks)
        etf_rate=0.0002,
        etf_fee=0.0,                 # c^E
        spanning=True,
        gamma=5.0,
        fund_cap=0.25, etf_cap=1.0, cash=1.0,
    ),
    # Positive net alpha, ETF trading at or above fund costs, a factor the ETFs miss.
    "fixed-income-style": dict(
        alpha_mean=0.0020,
        alpha_sd=0.0035,
        alpha_persistence=1.0,
        sigma_A=0.02,                # as registered in experiments 029-034's named points
        premium=(0.015, 0.005),
        premium_sd=(0.005, 0.005),
        factor_sd=(0.08, 0.04),
        fund_rate=0.0020,
        etf_rate=0.0050,
        etf_fee=0.0,
        spanning=False,              # experiment 027's "missing" menu; the formula checks set spanning per curve
        gamma=5.0,
        fund_cap=0.25, etf_cap=1.0, cash=1.0,
    ),
}

# Starting portfolios (fractions of wealth), as in experiment 027; "given" takes an explicit holding.
STARTS = {
    "all-ETF": dict(funds=0.0, market_etf=0.9),
    "all-fund": dict(funds=0.15, market_etf=0.0),
    "mixed": dict(funds=0.075, market_etf=0.45),
}

# Fair baselines every comparison reports (the human's item 1): ETF-only may sell funds, not buy them.
BASELINES = ["joint", "two-stage", "myopic", "dynamic", "ETF-only (sales allowed)", "funds-only"]
