"""Experiment 035: survivor-only estimates from the cached Yahoo data, ranges per class, and the approved formulas
evaluated at those ranges. Registered design: experiments/035-yahoo-pilot.md.  Run (after fetch.py):
uv run python experiments/035/estimate.py   (writes experiments/035/summary.json: derived statistics only)

Everything is survivor-only and illustrative (AGENTS.md rules 19, 22): these funds exist today.
"""
import hashlib
import importlib.util
import io
import json
import math
import zipfile
from pathlib import Path

import numpy as np
import pandas as pd
from scipy.stats import norm

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
CACHE = HERE / "cache"


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


m022 = _load("m022", ROOT / "experiments" / "022" / "model.py")
m003 = _load("m003", ROOT / "experiments" / "003" / "run.py")
presets = _load("presets", ROOT / "experiments" / "presets.py")
END = pd.Period("2025-06", freq="M")
GAMMA = 5.0


def ff5_monthly():
    """Monthly FF5 and RF from experiment 022's pinned file (same hash check)."""
    f = m022.CACHE / "ff5_2025-07cut.zip"
    m022.ff5_quarterly()                                     # fetches and verifies the pinned file if needed
    raw = f.read_bytes(); assert hashlib.sha256(raw).hexdigest() == m022.SHA
    text = zipfile.ZipFile(io.BytesIO(raw)).read("F-F_Research_Data_5_Factors_2x3.csv").decode("latin-1")
    rows, started = [], False
    for line in text.splitlines():
        s = line.strip()
        if s.startswith(",Mkt-RF"):
            if started:
                break
            started = True; continue
        if started:
            p = [x.strip() for x in s.split(",")]
            if len(p) == 7 and len(p[0]) == 6 and p[0].isdigit():
                rows.append([p[0]] + [float(x) / 100 for x in p[1:]])
            elif rows:
                break
    m = pd.DataFrame(rows, columns=["ym", "MktRF", "SMB", "HML", "RMW", "CMA", "RF"])
    m.index = pd.PeriodIndex(pd.to_datetime(m.pop("ym"), format="%Y%m"), freq="M")
    return m


def monthly_returns(t):
    d = pd.read_csv(CACHE / f"{t}_max.csv", skiprows=[1, 2], index_col=0)       # Deviation 3
    c = pd.to_numeric(d["Close"], errors="coerce").dropna()
    c.index = pd.PeriodIndex(pd.to_datetime(c.index), freq="M")
    c = c[c.index <= END]
    return c.pct_change().dropna()


def ols_nw(y, X, lags=3):
    X = np.column_stack([np.ones(len(X)), X])
    XtX_inv = np.linalg.inv(X.T @ X); b = XtX_inv @ X.T @ y; e = y - X @ b
    S = (X * e[:, None]).T @ (X * e[:, None])
    for l in range(1, lags + 1):
        w = 1 - l / (lags + 1)
        G = (X[l:] * e[l:, None]).T @ (X[:-l] * e[:-l, None])
        S += w * (G + G.T)
    V = XtX_inv @ S @ XtX_inv
    return b, np.sqrt(np.diag(V)), float(np.std(e, ddof=X.shape[1]))


def main():
    tick = json.load(open(HERE / "tickers.json"))
    ff = ff5_monthly()
    R = {t: monthly_returns(t) for g in tick.values() for t in g}
    dropped = {t: len(r) for t, r in R.items() if len(r) < 60}
    out = {"fetch_date": json.load(open(CACHE / "fetch_log.json"))["fetch_date"], "window_end": str(END), "dropped": dropped,
           "label": "survivor-only, illustrative (funds that exist today); no raw prices or returns stored"}
    # fixed-income factors from the ETFs
    rf = ff["RF"]
    fi = pd.DataFrame({"MKT_B": R["AGG"] - rf, "TERM": R["IEF"] - R["SHY"], "CREDIT": R["LQD"] - R["IEF"],
                       "HY": R["HYG"] - R["IEF"], "TIPS": R["TIP"] - R["IEF"]}).dropna()
    built = {"AGG": ["MKT_B"], "SHY": ["TERM"], "IEF": ["TERM", "CREDIT", "HY", "TIPS"], "LQD": ["CREDIT"], "HYG": ["HY"], "TIP": ["TIPS"], "BND": []}
    est = {}
    for cls, funds, etfs, F, names in (("equity", tick["equity_funds"], tick["equity_etfs"], ff[["MktRF", "SMB", "HML", "RMW", "CMA"]], None),
                                       ("fixed_income", tick["fi_funds"], tick["fi_etfs"], fi, None)):
        rows = {}
        for t in funds + etfs:
            if t in dropped:
                continue
            cols = list(F.columns)
            if cls == "fixed_income" and t in etfs:
                cols = [c for c in cols if c not in built[t]]
            d = pd.concat([R[t] - rf, F[cols]], axis=1, join="inner").dropna()
            d = d[d.index <= END]
            b, se, sres = ols_nw(d.iloc[:, 0].to_numpy(), d[cols].to_numpy())
            rows[t] = dict(kind="fund" if t in funds else "etf", months=len(d), start=str(d.index[0]), factors=cols,
                           alpha_q=float(3 * b[0]), alpha_se_q=float(3 * se[0]), resid_sd_q=float(sres * math.sqrt(3)),
                           loadings={c: float(v) for c, v in zip(cols, b[1:])}, built_from_it=[c for c in F.columns if c not in cols])
        fund_rows = [rows[t] for t in funds if t in rows]
        a = np.array([r["alpha_q"] for r in fund_rows]); s = np.array([r["alpha_se_q"] for r in fund_rows]); sd = np.array([r["resid_sd_q"] for r in fund_rows])
        rng = lambda x: dict(min=float(x.min()), median=float(np.median(x)), max=float(x.max()))
        summ = dict(alpha_q=rng(a), alpha_se_q=rng(s), resid_sd_q=rng(sd), alpha_cross_sd=float(a.std(ddof=1)),
                    prior_sd_illustrative=float(math.sqrt(max(0.0, a.var(ddof=1) - float(np.mean(s ** 2))))),
                    etf_resid_sd_q=rng(np.array([rows[t]["resid_sd_q"] for t in etfs if t in rows])))
        est[cls] = dict(rows=rows, summary=summ)
    # fixed-income spanning: share of each fund's factor variance not hedgeable by {AGG, IEF, LQD}
    Sf = fi.cov().to_numpy() * 3
    full = list(fi.columns)
    BE = []
    for t in ("AGG", "IEF", "LQD"):
        d = pd.concat([R[t] - rf, fi], axis=1, join="inner").dropna()
        b, _, _ = ols_nw(d.iloc[:, 0].to_numpy(), d[full].to_numpy()); BE.append(b[1:])
    BE = np.array(BE)
    span = {}
    for t in tick["fi_funds"]:
        if t in dropped:
            continue
        d = pd.concat([R[t] - rf, fi], axis=1, join="inner").dropna()
        b, _, _ = ols_nw(d.iloc[:, 0].to_numpy(), d[full].to_numpy()); bA = b[1:]
        tot = float(bA @ Sf @ bA); cov = BE @ Sf @ bA; hedged = float(cov @ np.linalg.solve(BE @ Sf @ BE.T, cov))
        span[t] = dict(factor_var_q=tot, unhedgeable_share=float((tot - hedged) / tot) if tot > 0 else None)
    out["fi_spanning_menu"] = ["AGG", "IEF", "LQD"]; out["fi_unspanned_share"] = span
    # ETF expense ratios via experiment 003's route (SEC risk/return summaries, 2025 filings)
    mf = json.load(open(CACHE / "company_tickers_mf.json")); f = mf["fields"]
    cls_of = {row[f.index("symbol")]: row[f.index("classId")] for row in mf["data"]}
    exp = {}
    try:
        snap, _ = m003.snapshot(2025, {})
        for t in tick["equity_etfs"] + tick["fi_etfs"] + tick["equity_funds"] + tick["fi_funds"]:
            c = cls_of.get(t)
            v = snap.loc[c, "expense"] if (c is not None and c in snap.index and "expense" in snap.columns) else float("nan")
            exp[t] = None if (v is None or (isinstance(v, float) and math.isnan(v))) else float(v)
    except Exception as e:                                # recorded, not hidden
        exp = {"error": repr(e)}
    out["expense_ratio_annual"] = exp
    out["estimates"] = est
    # thresholds at the ranges (formulas only)
    th = {}
    for cls, pre in (("equity", presets.PRESETS["equity-style"]), ("fixed_income", presets.PRESETS["fixed-income-style"])):
        S_ = est[cls]["summary"]; kap = pre["fund_rate"]
        rows = []
        for q in ("min", "median", "max"):
            for var in ("alpha_q", "alpha_se_q", "resid_sd_q"):
                a = S_["alpha_q"][q] if var == "alpha_q" else pre["alpha_mean"]
                se = S_["alpha_se_q"][q] if var == "alpha_se_q" else S_["alpha_se_q"]["median"]
                sig = S_["resid_sd_q"][q] if var == "resid_sd_q" else pre["sigma_A"]
                v = sig ** 2 + se ** 2
                for xm in (0.0, 0.1):
                    p = a - kap - GAMMA * v * xm
                    cap = 0.25                               # Deviation 3: claim 106's cap form at the presets' fund cap, beside the uncapped value
                    cm_cap = 0.0 if p <= 0 else ((p ** 2 / (2 * GAMMA * v)) if p / (GAMMA * v) <= cap - xm else (p * (cap - xm) - 0.5 * GAMMA * v * (cap - xm) ** 2))
                    rows.append(dict(vary=var, at=q, xm=xm, alpha=a, se=se, sigma=sig, buy=bool(p > 0), purchase_excess=p,
                                     C_minus_bp=(p ** 2 / (2 * GAMMA * v) * 1e4 if p > 0 else 0.0), C_minus_cap_bp=cm_cap * 1e4))
        z = norm.isf(0.05)
        n = {q: {f"{d * 100:.2f}%": math.ceil(4 * S_["resid_sd_q"][q] ** 2 * z ** 2 / d ** 2) for d in (0.0005, 0.001)} for q in ("min", "median", "max")}
        th[cls] = dict(preset_fund_rate=kap, preset_alpha=pre["alpha_mean"], preset_sigma_A=pre["sigma_A"], rows=rows, claim039_quarters=n)
    out["thresholds"] = th
    json.dump(out, open(HERE / "summary.json", "w"), indent=1)
    print(json.dumps({k: out[k] for k in ("dropped", "fi_unspanned_share", "expense_ratio_annual")}, indent=1))
    for cls in est:
        print(cls, json.dumps(est[cls]["summary"], indent=1))
        for t, r in est[cls]["rows"].items():
            print(f"  {t:6s} {r['kind']:4s} {r['start']} n={r['months']:3d} alpha_q {r['alpha_q'] * 100:+.3f}% (SE {r['alpha_se_q'] * 100:.3f}) resid_q {r['resid_sd_q'] * 100:.2f}% built-from {r['built_from_it']}")
    print(json.dumps(th, indent=1)[:3000])


if __name__ == "__main__":
    main()
