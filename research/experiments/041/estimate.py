"""Experiment 041: estimates, input distributions, the empirical prior and the approved theorems at those ranges.
Registered design: experiments/041-larger-pilot.md.  Run (after universe.py and fetch.py):
uv run python experiments/041/estimate.py   (writes experiments/041/summary.json: derived statistics only)

Survivor-only and illustrative (AGENTS.md rules 19, 22). Alphas are net of fees, against implementable factors.
"""
import hashlib
import importlib.util
import io
import json
import math
import zipfile
from collections import defaultdict
from pathlib import Path

import numpy as np
import pandas as pd
from scipy.stats import norm

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
CACHE = HERE / "cache"
_s = importlib.util.spec_from_file_location("e035", ROOT / "experiments" / "035" / "estimate.py"); e035 = importlib.util.module_from_spec(_s); _s.loader.exec_module(e035)
_s = importlib.util.spec_from_file_location("m003", ROOT / "experiments" / "003" / "run.py"); m003 = importlib.util.module_from_spec(_s); _s.loader.exec_module(m003)
END = pd.Period("2025-06", freq="M")
GAMMA = 5.0
KAPPAS = [0.0, 0.001, 0.005]
BOND_F = ["MKT_B", "TERM", "LONG", "CREDIT", "HY", "TIPS", "MUNI"]
BUILT = {"AGG": ["MKT_B"], "SHY": ["TERM"], "IEF": ["TERM", "LONG", "CREDIT", "HY", "TIPS", "MUNI"], "TLT": ["LONG"], "LQD": ["CREDIT"],
         "HYG": ["HY"], "TIP": ["TIPS"], "MUB": ["MUNI"]}


def french_csv(raw):
    text = zipfile.ZipFile(io.BytesIO(raw)).read(zipfile.ZipFile(io.BytesIO(raw)).namelist()[0]).decode("latin-1")
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


def returns(t):
    p = CACHE / f"{t}.csv"
    if not p.exists():
        return None
    d = pd.read_csv(p, skiprows=[1, 2], index_col=0)
    if "Close" not in d.columns or d.empty:
        return None
    c = pd.to_numeric(d["Close"], errors="coerce").dropna()
    if c.empty:
        return None
    c.index = pd.PeriodIndex(pd.to_datetime(c.index), freq="M")
    return c[c.index <= END].pct_change().dropna()


def q(x, ps=(0.1, 0.25, 0.5, 0.75, 0.9)):
    x = np.asarray([v for v in x if v is not None and not (isinstance(v, float) and math.isnan(v))], float)
    return {f"p{int(p * 100)}": float(np.quantile(x, p)) for p in ps} if len(x) else None


def main():
    U = json.load(open(HERE / "universe.json")); log = json.load(open(CACHE / "fetch_log.json"))
    ff = e035.ff5_monthly()
    dev = french_csv((CACHE / "developed_ex_us_5.zip").read_bytes())
    R = {f["ticker"]: returns(f["ticker"]) for f in U["funds"]}
    R["IWM"] = returns("IWM")                                    # Deviation 3: menu only
    rf = ff["RF"]
    bond = pd.DataFrame({"MKT_B": R["AGG"] - rf, "TERM": R["IEF"] - R["SHY"], "LONG": R["TLT"] - R["IEF"], "CREDIT": R["LQD"] - R["IEF"],
                         "HY": R["HYG"] - R["IEF"], "TIPS": R["TIP"] - R["IEF"], "MUNI": R["MUB"] - R["IEF"]}).dropna()
    FS = {"us_equity": ff[["MktRF", "SMB", "HML", "RMW", "CMA"]], "intl_equity": dev[["MktRF", "SMB", "HML", "RMW", "CMA"]], "bond": bond, "muni": bond}
    snap, _ = m003.snapshot(2025, {})
    rows, dropped = [], {}
    for f in U["funds"]:
        t = f["ticker"]; r = R.get(t)
        if f["cls"] is None or r is None:
            dropped[t] = "no data" if r is None else "no class"; continue
        F = FS[f["cls"]]; cols = [c for c in F.columns if c not in BUILT.get(t, [])]
        d = pd.concat([r - rf, F[cols]], axis=1, join="inner").dropna(); d = d[d.index <= END]
        if len(d) < 60:
            dropped[t] = f"{len(d)} months"; continue
        b, se, sres = e035.ols_nw(d.iloc[:, 0].to_numpy(), d[cols].to_numpy())
        cid = f.get("class_id")
        load = lambda k: None if (cid is None or cid not in snap.index or k not in snap.columns or pd.isna(snap.loc[cid, k])) else float(snap.loc[cid, k])
        rows.append(dict(ticker=t, group=f["group"], cls=f["cls"], cat=f["cat"], months=len(d), start=str(d.index[0]), factors=cols,
                         alpha_q=float(3 * b[0]), se_q=float(3 * se[0]), sres_q=float(sres * math.sqrt(3)), loadings=[float(v) for v in b[1:]],
                         expense=f.get("expense"), front=load("front"), deferred=load("deferred")))
    out = dict(fetch_date=log["fetch_date"], developed_ex_us_sha256=log["developed_ex_us_sha256"], dropped=dropped, n=len(rows),
               bond_factor_start=str(bond.index[0]), label="survivor-only, illustrative; alphas net of fees against implementable factors")
    # distributions
    dist = {}
    for g in ("active", "index_mf", "etf"):
        for c in ("us_equity", "intl_equity", "bond", "muni"):
            rs = [r for r in rows if r["group"] == g and r["cls"] == c]
            if rs:
                dist[f"{g}/{c}"] = dict(n=len(rs), alpha_q=q([r["alpha_q"] for r in rs]), se_q=q([r["se_q"] for r in rs]), sres_q=q([r["sres_q"] for r in rs]),
                                        expense=q([r["expense"] for r in rs]), front_load_nonzero=sum(1 for r in rs if (r["front"] or 0) > 0),
                                        deferred_nonzero=sum(1 for r in rs if (r["deferred"] or 0) > 0), mkt_beta=q([r["loadings"][0] for r in rs]))
    out["distributions"] = dist
    # empirical prior (active funds)
    prior = {}
    rng = np.random.default_rng([2041, 0])
    for c in ("us_equity", "intl_equity", "bond", "muni"):
        rs = [r for r in rows if r["group"] == "active" and r["cls"] == c]
        a = np.array([r["alpha_q"] for r in rs]); s = np.array([r["se_q"] for r in rs])
        s2 = lambda a_, s_: max(0.0, float(np.var(a_, ddof=1) - np.mean(s_ ** 2)))
        boot = [s2(a[ix], s[ix]) for ix in (rng.integers(0, len(a), len(a)) for _ in range(1000))]
        prior[c] = dict(n=len(rs), m=float(a.mean()), s=math.sqrt(s2(a, s)), s_lo=math.sqrt(float(np.quantile(boot, 0.05))), s_hi=math.sqrt(float(np.quantile(boot, 0.95))),
                        cross_sd=float(a.std(ddof=1)), mean_se=float(np.sqrt(np.mean(s ** 2))))
    out["prior"] = prior
    # posterior beliefs and the theorems
    th = defaultdict(dict)
    z = norm.isf(0.05)
    for r in rows:
        if r["group"] != "active":
            continue
        P = prior[r["cls"]]; s2 = P["s"] ** 2
        if s2 > 0:
            w = s2 / (s2 + r["se_q"] ** 2); r["alpha_post"] = P["m"] + w * (r["alpha_q"] - P["m"]); r["p"] = 1 / (1 / s2 + 1 / r["se_q"] ** 2)
        else:
            r["alpha_post"] = P["m"]; r["p"] = 0.0
        r["v"] = r["sres_q"] ** 2 + r["p"]
    for c in ("us_equity", "intl_equity", "bond", "muni"):
        rs = [r for r in rows if r["group"] == "active" and r["cls"] == c]
        for k in KAPPAS:
            pe = [r["alpha_post"] - k - (r["front"] or 0.0) for r in rs]
            CAP = 0.25                                   # Deviation 4: claim 106's cap form at the presets' fund cap
            Cm = [(p ** 2 / (2 * GAMMA * r["v"]) if p / (GAMMA * r["v"]) <= CAP else p * CAP - 0.5 * GAMMA * r["v"] * CAP ** 2) for p, r in zip(pe, rs) if p > 0]
            gap = [abs(r["alpha_post"] - k) for r in rs]
            nneed = [4 * r["sres_q"] ** 2 * z ** 2 / g ** 2 if g > 0 else math.inf for g, r in zip(gap, rs)]
            cert = [r["months"] / 3 >= n for n, r in zip(nneed, rs)]
            th[c][f"kappa_{int(k * 1e4)}bp"] = dict(n=len(rs), share_bought=float(np.mean([p > 0 for p in pe])), Cminus_bp_median_if_bought=float(np.median(Cm) * 1e4) if Cm else 0.0,
                                                   Cminus_bp_sum=float(np.sum(Cm) * 1e4), n_needed_quarters=q([n for n in nneed if n < math.inf]),
                                                   history_quarters=q([r["months"] / 3 for r in rs]), share_certifiable=float(np.mean(cert)))
        kap = np.array([r["p"] / (r["sres_q"] ** 2 + r["p"]) for r in rs])
        th[c]["kalman_gain"] = q(kap)
        th[c]["share_gain_over_theta"] = {f"{th_}": float(np.mean(kap > th_ / (1 + th_))) for th_ in (0.01, 0.05)}
        th[c]["anticipation_bound"] = {f"Dur{D}": q((kap / (1 - kap)) ** 2 * D) for D in (1, 3, 5)}
    # claim 105: unhedgeable shares against the stated menus; premium-error holding shift
    def menu_stats(c, menu, F):
        Sf = F.cov().to_numpy() * 3; n_q = len(F) / 3
        se_prem = np.sqrt(np.diag(Sf) / n_q)                          # one-SD premium error (sample-mean SE, quarterly)
        BE = []
        for t in menu:
            d = pd.concat([R[t] - rf, F], axis=1, join="inner").dropna()
            b, _, _ = e035.ols_nw(d.iloc[:, 0].to_numpy(), d[list(F.columns)].to_numpy()); BE.append(b[1:])
        BE = np.array(BE)
        Q_, _ = np.linalg.qr(BE.T); PiR = Q_ @ Q_.T; PiU = np.eye(len(Sf)) - PiR
        SRR, SRU, SUU = PiR @ Sf @ PiR, PiR @ Sf @ PiU, PiU @ Sf @ PiU
        SRRi = np.linalg.pinv(SRR); J = PiU - PiR @ SRRi @ SRU; schur = SUU - SRU.T @ SRRi @ SRU
        res = []
        for r in rows:
            if r["group"] != "active" or r["cls"] != c or len(r["loadings"]) != len(Sf):
                continue
            b = np.array(r["loadings"]); tot = float(b @ Sf @ b); cov = BE @ Sf @ b
            hedged = float(cov @ np.linalg.solve(BE @ Sf @ BE.T, cov))
            sred = r["v"] + float(b @ schur @ b)
            shift = float(np.sqrt(np.sum(((J @ b) * se_prem) ** 2))) / (GAMMA * sred)
            res.append(dict(unhedgeable=(tot - hedged) / tot if tot > 0 else None, shift=shift))
        return dict(menu=menu, unhedgeable_share=q([x["unhedgeable"] for x in res]), holding_shift_per_sd=q([x["shift"] for x in res]), n=len(res),
                    share_shift_over_0_1=float(np.mean([x["shift"] > 0.1 for x in res])))
    out["claim105"] = {"us_equity": menu_stats("us_equity", ["SPY", "IWM", "VTV", "VUG"], FS["us_equity"]),
                       "bond": menu_stats("bond", ["AGG", "IEF", "LQD"], FS["bond"]), "muni": menu_stats("muni", ["AGG", "IEF", "LQD"], FS["bond"])}
    # claim 104: L_E^2 / (2 gamma) with a spanning menu (one ETF per factor), fees at the ETF expense-ratio range
    c104 = {}
    for c, F in (("us_equity", FS["us_equity"]), ("bond", FS["bond"])):
        Sf = F.cov().to_numpy() * 3; St = Sf + Sf / (len(F) / 3); K = len(Sf)
        w_, U_ = np.linalg.eigh(St); Sih = U_ @ np.diag(w_ ** -0.5) @ U_.T; nrm = np.linalg.norm(Sih, 2)
        fees = [r["expense"] for r in rows if r["group"] == "etf" and r["cls"] == c and r["expense"] is not None]
        fq = q(fees, (0.1, 0.5, 0.9))
        c104[c] = {f"fee_{k}_{int(kE * 1e4)}bp": float((nrm * (math.sqrt(K) * fq[k] / 4 + math.sqrt(K) * kE)) ** 2 / (2 * GAMMA) * 1e4)
                   for k in ("p10", "p50", "p90") for kE in (0.0, 0.0005, 0.0025)}
        c104[c]["etf_fee_annual"] = fq
    out["claim104_bound_bp"] = c104
    out["theorems"] = th
    out["funds"] = [{k: r[k] for k in ("ticker", "group", "cls", "cat", "months", "start", "alpha_q", "se_q", "sres_q", "expense", "front", "deferred") } | ({"alpha_post": r["alpha_post"]} if "alpha_post" in r else {}) for r in rows]
    json.dump(out, open(HERE / "summary.json", "w"), indent=1)
    print(json.dumps({k: out[k] for k in ("n", "dropped", "bond_factor_start", "prior")}, indent=1))


if __name__ == "__main__":
    main()
