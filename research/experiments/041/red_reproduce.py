"""Red's reproduction of experiment 041's estimates and readings, written without reading fetch.py, estimate.py or report.py.
It takes the universe as committed (universe.json, fixed by rule before any return was fetched), fetches Yahoo monthly
adjusted closes itself (1 request per second) into a cache outside the repository (argument 1, which must also hold the
pinned FF5 zip and the Developed ex US zip; both hashes checked), and recomputes the class distributions, the empirical
prior and the approved theorems' readings. No data is committed."""
import sys, os, io, time, zipfile, hashlib, json
import numpy as np, pandas as pd
from scipy.stats import norm

CACHE = sys.argv[1]; END = pd.Period("2025-06", "M"); GAM = 5.0
FF5_SHA = "42492fc7fe23de2c44058e77414e1d35c451bf8d289dfff75c5b80c2804324e2"; DEV_SHA_PREFIX = "b03fcabd"


def fetch(t):
    f = os.path.join(CACHE, f"red41_{t}.csv")
    if not os.path.exists(f):
        import yfinance as yf
        try: d = yf.Ticker(t).history(period="max", interval="1mo", auto_adjust=True)
        except Exception: d = pd.DataFrame()
        (d[["Close"]] if len(d) else pd.DataFrame({"Close": []})).to_csv(f); time.sleep(1.0)
    d = pd.read_csv(f, index_col=0)
    if len(d) == 0: return None
    d.index = pd.to_datetime(d.index, utc=True).tz_convert(None).to_period("M")
    return d["Close"].groupby(level=0).last().pct_change().dropna()


def french(path, sha=None, prefix=None):
    raw = open(path, "rb").read(); h = hashlib.sha256(raw).hexdigest()
    assert (sha is None or h == sha) and (prefix is None or h.startswith(prefix)), path
    z = zipfile.ZipFile(io.BytesIO(raw)); txt = z.read(z.namelist()[0]).decode("latin-1").splitlines()
    start = next(i for i, l in enumerate(txt) if l.replace(" ", "").startswith(",Mkt-RF")); rows = []
    for line in txt[start + 1:]:
        p = [x.strip() for x in line.split(",")]
        if len(p) < 7 or not p[0].isdigit() or len(p[0]) != 6: break
        rows.append([p[0]] + [float(x) / 100 for x in p[1:7]])
    df = pd.DataFrame(rows, columns=["ym", "Mkt-RF", "SMB", "HML", "RMW", "CMA", "RF"])
    df.index = pd.PeriodIndex(pd.to_datetime(df["ym"], format="%Y%m"), freq="M"); return df.drop(columns="ym")


def reg(y, X, lags=3):
    d = pd.concat([y.rename("y"), X], axis=1, join="inner").dropna(); d = d[d.index <= END]
    Xm = np.column_stack([np.ones(len(d)), d.drop(columns="y").values]); yv = d["y"].values; n, k = Xm.shape
    XtXi = np.linalg.inv(Xm.T @ Xm); beta = XtXi @ Xm.T @ yv; e = yv - Xm @ beta; u = Xm * e[:, None]; Sm = u.T @ u
    for L in range(1, lags + 1):
        G = u[L:].T @ u[:-L]; Sm += (1 - L / (lags + 1)) * (G + G.T)
    V = XtXi @ Sm @ XtXi
    return dict(alpha=3 * beta[0], se=3 * np.sqrt(V[0, 0]), rsd=np.sqrt(3) * np.sqrt(e @ e / (n - k)), n=n, b=pd.Series(beta[1:], index=d.drop(columns="y").columns))


def unhedged(b, E, Sf):
    A = E @ Sf @ E.T; h = np.linalg.lstsq(A, E @ Sf @ b, rcond=None)[0]; r = b - E.T @ h
    return float(r @ Sf @ r / (b @ Sf @ b))


def main():
    U = json.load(open("experiments/041/universe.json"))["funds"]
    F5 = french(os.path.join(CACHE, "ff5_2025-07cut.zip"), sha=FF5_SHA); DX = french(os.path.join(CACHE, "developed_ex_us_5.zip"), prefix=DEV_SHA_PREFIX)
    need = sorted(set([f["ticker"] for f in U] + ["AGG", "IEF", "SHY", "TLT", "LQD", "HYG", "TIP", "MUB", "SPY", "IWM", "VTV", "VUG"]))
    R = {t: fetch(t) for t in need}
    rf = F5["RF"]
    B = pd.DataFrame({"MKT_B": R["AGG"] - rf, "TERM": R["IEF"] - R["SHY"], "LONG": R["TLT"] - R["IEF"], "CREDIT": R["LQD"] - R["IEF"],
                      "HY": R["HYG"] - R["IEF"], "TIPS": R["TIP"] - R["IEF"], "MUNI": R["MUB"] - R["IEF"]}).dropna()
    B = B[B.index <= END]
    built = {"AGG": ["MKT_B"], "IEF": ["TERM", "LONG", "CREDIT", "HY", "TIPS", "MUNI"], "SHY": ["TERM"], "TLT": ["LONG"], "LQD": ["CREDIT"], "HYG": ["HY"], "TIP": ["TIPS"], "MUB": ["MUNI"]}
    rows = []; dropped = 0
    for f in U:
        r = R.get(f["ticker"])
        if r is None or len(r[r.index <= END]) < 60: dropped += 1; continue
        cls = f["cls"]
        if cls == "us_equity": X = F5[["Mkt-RF", "SMB", "HML", "RMW", "CMA"]]; y = r - rf
        elif cls in ("intl_equity", "international_equity"): X = DX[["Mkt-RF", "SMB", "HML", "RMW", "CMA"]]; y = r - DX["RF"]
        else: X = B.drop(columns=built.get(f["ticker"], [])); y = r - rf
        e = reg(y, X); rows.append(dict(f, **{k: v for k, v in e.items() if k != "b"}, b=e["b"]))
    D = pd.DataFrame(rows)
    print(f"universe {len(U)} tickers; kept {len(D)} (dropped {dropped}); classes: " + ", ".join(f"{g}/{c}: {n}" for (g, c), n in D.groupby(['group', 'cls']).size().items()))
    q = lambda s: f"{np.percentile(s, 10) * 100:+.2f} / {np.percentile(s, 50) * 100:+.2f} / {np.percentile(s, 90) * 100:+.2f}%"
    for (g, c), G in D.groupby(["group", "cls"]):
        if len(G) >= 5: print(f"  {g} {c} (n {len(G)}): alpha {q(G.alpha)}; SE {q(G.se)}; residual SD {q(G.rsd)}")
    print("empirical prior, active:")
    A = D[D.group == "active"]; out = {}
    for c, G in A.groupby("cls"):
        m = G.alpha.mean(); s2 = max(0.0, G.alpha.var(ddof=1) - np.mean(G.se ** 2)); out[c] = (m, s2)
        print(f"  {c}: m {m * 100:+.3f}%, s {np.sqrt(s2) * 100:.3f}%")
    z = norm.isf(0.05)
    for c, G in A.groupby("cls"):
        m, s2 = out[c]; se2 = G.se.values ** 2
        post = m + (s2 / (s2 + se2)) * (G.alpha.values - m) if s2 > 0 else np.full(len(G), m)
        p = 1 / (1 / s2 + 1 / se2) if s2 > 0 else np.zeros(len(G)); v = G.rsd.values ** 2 + p
        line = f"  {c}: bought at 0/10/50 bp: " + " / ".join(f"{np.mean(post - k > 0) * 100:.0f}%" for k in (0, 0.001, 0.005))
        pk = post - 0.0; bought = pk > 0
        if bought.any():
            lo = pk / (GAM * v); Cm = np.where(lo <= 0.25, pk ** 2 / (2 * GAM * v), pk * 0.25 - GAM * v / 2 * 0.0625)
            line += f"; ETF-only cost (median over bought, cap 0.25, 0 bp) {np.median(Cm[bought]) * 1e4:.2f} bp"
        gain = p / (G.rsd.values ** 2 + p); hist = G.n.values / 3
        for k in (0.0, 0.005):
            n_need = 4 * G.rsd.values ** 2 * z ** 2 / np.maximum(np.abs(post - k), 1e-12) ** 2
            line += f"; certify at {k * 1e4:.0f} bp: median need {np.median(n_need):,.0f} q, share certifiable {np.mean(n_need <= hist) * 100:.0f}%"
        line += f"; median Kalman gain {np.median(gain):.4f}, share > 1/101 {np.mean(gain > 0.01 / 1.01) * 100:.0f}%, median history {np.median(hist):.0f} q"
        print(line)
    # claim 105: unhedgeable share of factor variance, active funds, against the stated menus
    for c, menu, X in [("us_equity", ["SPY", "IWM", "VTV", "VUG"], F5[["Mkt-RF", "SMB", "HML", "RMW", "CMA"]]), ("bond", ["AGG", "IEF", "LQD"], B), ("muni", ["AGG", "IEF", "LQD"], B)]:
        Sf = (X[X.index <= END].dropna().cov() * 3).values
        E = np.array([reg(R[t] - rf, X)["b"].reindex(X.columns).fillna(0).values for t in menu])
        G = A[A.cls == c]
        if len(G) == 0: continue
        sh = [unhedged(b.reindex(X.columns).fillna(0).values, E, Sf) for b in G.b]
        print(f"  claim 105, {c} vs {menu}: unhedgeable share median {np.median(sh) * 100:.2f}%, p90 {np.percentile(sh, 90) * 100:.2f}%")


if __name__ == "__main__":
    main()
