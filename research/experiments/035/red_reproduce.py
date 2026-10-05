"""Red's reproduction of experiment 035 (survivor-only Yahoo pilot), written without reading fetch.py, estimate.py
or report.py. Fetches monthly adjusted closes itself (1 request per second) into a cache outside the repository
(argument 1), reads the pinned French five-factor file (SHA-256 checked), and recomputes the Design's estimates.
No data is committed."""
import sys, os, io, time, zipfile, hashlib, json
import numpy as np, pandas as pd

CACHE = sys.argv[1]
FF5 = os.path.join(CACHE, "ff5_2025-07cut.zip"); FF5_SHA = "42492fc7fe23de2c44058e77414e1d35c451bf8d289dfff75c5b80c2804324e2"
EQ_F = ["AGTHX", "FCNTX", "DODGX", "PRBLX", "VPMCX", "TRBCX"]; EQ_E = ["SPY", "IVV", "VTV", "VUG", "IWM", "MTUM", "QUAL"]
FI_F = ["PTTRX", "DODIX", "MWTRX", "FTBFX", "PRCIX", "LSBRX"]; FI_E = ["AGG", "BND", "SHY", "IEF", "LQD", "HYG", "TIP"]
END = pd.Period("2025-06", "M")


def fetch(t):
    f = os.path.join(CACHE, f"red_{t}.csv")
    if not os.path.exists(f):
        import yfinance as yf
        d = yf.Ticker(t).history(period="max", interval="1mo", auto_adjust=True)
        d[["Close"]].to_csv(f); time.sleep(1.0)
    d = pd.read_csv(f, index_col=0)
    d.index = pd.to_datetime(d.index, utc=True).tz_convert(None).to_period("M")
    c = d["Close"].groupby(level=0).last()
    return c.pct_change().dropna()


def ff5():
    assert hashlib.sha256(open(FF5, "rb").read()).hexdigest() == FF5_SHA
    z = zipfile.ZipFile(FF5); txt = z.read(z.namelist()[0]).decode("latin-1").splitlines()
    rows = []
    for line in txt[txt.index(next(l for l in txt if l.startswith(",Mkt-RF"))) + 1:]:
        p = line.split(",")
        if len(p) < 7 or not p[0].strip().isdigit() or len(p[0].strip()) != 6: break
        rows.append([p[0].strip()] + [float(x) / 100 for x in p[1:7]])
    df = pd.DataFrame(rows, columns=["ym", "Mkt-RF", "SMB", "HML", "RMW", "CMA", "RF"])
    df.index = pd.PeriodIndex(pd.to_datetime(df["ym"], format="%Y%m"), freq="M"); return df.drop(columns="ym")


def reg(y, X, lags=3):
    """OLS with a Newey-West (Bartlett, 3 lags) covariance, coded here."""
    d = pd.concat([y.rename("y"), X], axis=1, join="inner").dropna(); d = d[d.index <= END]
    Xm = np.column_stack([np.ones(len(d)), d.drop(columns="y").values]); yv = d["y"].values; n, k = Xm.shape
    XtXi = np.linalg.inv(Xm.T @ Xm); beta = XtXi @ Xm.T @ yv; e = yv - Xm @ beta
    u = Xm * e[:, None]; Sm = u.T @ u
    for L in range(1, lags + 1):
        G = u[L:].T @ u[:-L]; Sm += (1 - L / (lags + 1)) * (G + G.T)
    V = XtXi @ Sm @ XtXi
    b = pd.Series(beta[1:], index=d.drop(columns="y").columns)
    return dict(alpha=3 * beta[0], se=3 * np.sqrt(V[0, 0]), se_nd=3 * np.sqrt(V[0, 0] * n / (n - k)), rsd=np.sqrt(3) * np.sqrt(e @ e / (n - k)),
                n=n, start=str(d.index[0]), b=b)


def main():
    F = ff5(); rf = F["RF"]; R = {t: fetch(t) for t in EQ_F + EQ_E + FI_F + FI_E}
    out = {}
    eq = {t: reg(R[t] - rf, F[["Mkt-RF", "SMB", "HML", "RMW", "CMA"]]) for t in EQ_F}
    eqE = {t: reg(R[t] - rf, F[["Mkt-RF", "SMB", "HML", "RMW", "CMA"]])["rsd"] for t in EQ_E}
    B = pd.DataFrame({"MKT_B": R["AGG"] - rf, "TERM": R["IEF"] - R["SHY"], "CREDIT": R["LQD"] - R["IEF"], "HY": R["HYG"] - R["IEF"], "TIPS": R["TIP"] - R["IEF"]}).dropna()
    B = B[(B.index >= pd.Period("2007-05", "M")) & (B.index <= END)]
    fi = {t: reg(R[t] - rf, B) for t in FI_F}
    built = {"AGG": ["MKT_B"], "SHY": ["TERM"], "IEF": ["TERM", "CREDIT", "HY", "TIPS"], "LQD": ["CREDIT"], "HYG": ["HY"], "TIP": ["TIPS"], "BND": []}
    fiE = {t: reg(R[t] - rf, B.drop(columns=built[t]))["rsd"] for t in FI_E}
    for name, d, dE in [("equity", eq, eqE), ("fixed income", fi, fiE)]:
        a = np.array([v["alpha"] for v in d.values()]); se = np.array([v["se"] for v in d.values()]); rs = np.array([v["rsd"] for v in d.values()])
        prior = np.sqrt(max(0.0, a.var(ddof=1) - np.mean(se ** 2)))
        print(f"{name}: alpha {a.min()*100:+.2f}% / {np.median(a)*100:+.2f}% / {a.max()*100:+.2f}%; SE {se.min()*100:.2f}-{se.max()*100:.2f}%; residual SD {rs.min()*100:.2f}-{rs.max()*100:.2f}%; "
              f"cross-sectional SD {a.std(ddof=1)*100:.2f}%; prior {prior*100:.2f}%; ETF residual SD {min(dE.values())*100:.2f}-{max(dE.values())*100:.2f}%; "
              f"windows {sorted(set(v['start'] for v in d.values()))[:3]}.., months {min(v['n'] for v in d.values())}-{max(v['n'] for v in d.values())}")
        out[name] = dict(a=a, se=se, rs=rs)
    # spanning: ETFs AGG, IEF, LQD placed in bond-factor space by regression on all five factors
    Sf = B.cov().values * 3
    E = np.array([reg(R[t] - rf, B)["b"].values for t in ["AGG", "IEF", "LQD"]])
    shares = {}
    for t in FI_F:
        b = fi[t]["b"].values
        # min over h of (b - E'h)' Sf (b - E'h), relative to b' Sf b
        A = E @ Sf @ E.T; h = np.linalg.solve(A, E @ Sf @ b); res = b - E.T @ h
        shares[t] = float(res @ Sf @ res / (b @ Sf @ b))
    print("unhedgeable share by {AGG, IEF, LQD}: " + ", ".join(f"{t} {100*s:.1f}%" for t, s in shares.items()))
    # formulas at the ranges (presets)
    from scipy.stats import norm
    z = norm.isf(0.05)
    for name, rate, gam, sA in [("equity", 0.005, 5.0, 0.02), ("fixed income", 0.002, 5.0, 0.02)]:
        o = out[name]; seM = np.median(o["se"]); v = sA ** 2 + seM ** 2
        for lab, a in [("min", o["a"].min()), ("median", np.median(o["a"])), ("max", o["a"].max())]:
            for x0 in [0, 0.1]:
                p = a - rate - gam * v * x0; C = p * p / (2 * gam * v) if p > 0 else 0.0
                lo = p / (gam * v) + x0; Ccap = (p * (0.25 - x0) - gam * v / 2 * (0.25 - x0) ** 2) if (p > 0 and lo > 0.25) else C
                print(f"  {name} {lab} alpha {a*100:+.3f}%, x^- {x0}: excess {p*1e4:+.1f} bp, C^- {C*1e4:.2f} bp (cap-0.25 form {Ccap*1e4:.2f} bp)")
        for d in [0.0005, 0.001]:
            n = [4 * s ** 2 * z ** 2 / d ** 2 for s in (o["rs"].min(), o["rs"].max())]
            print(f"  {name} claim 039 n, gap {d*100:.2f}%: {n[0]:,.0f}-{n[1]:,.0f} quarters")


if __name__ == "__main__":
    main()
