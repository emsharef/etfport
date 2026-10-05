"""Experiment 001: switching-cost materiality (see experiments/001-switching-cost-materiality.md).

Deterministic. Cost rates are assumed (labelled in the experiment file); factor statistics come from the
Kenneth French library 3-factor file pinned to the archived July 2025 cut, cached under cache/ and never
committed. Prints every table in Markdown.
"""
from __future__ import annotations

import hashlib
import io
import math
import urllib.parse
import urllib.request
import zipfile
from pathlib import Path

import pandas as pd

HERE = Path(__file__).resolve().parent
CACHE = HERE / "cache"
BASE = "https://mba.tuck.dartmouth.edu/pages/faculty/ken.french/Data_Library/"  # archive hrefs are relative to Data_Library/
PINNED = "Historical_Archives/08 2025 Update/ftp/F-F_Research_Data_Factors_CSV.zip"
BP = 1e-4

# Part B: assumed one-way rates (fractions of the traded amount): kA_b, kA_s, kE (ETF buy = sell).
CASES = [
    ("Z", 0, 0, 0, "yes"),
    ("EQ5", 5, 5, 5, "yes"),
    ("EQ25", 25, 25, 25, "yes"),
    ("NTF-liquid", 0, 0, 1, "yes"),
    ("NTF-niche", 0, 0, 25, "yes"),
    ("ETF-stress", 0, 0, 100, "yes"),
    ("TF-10k", 50, 50, 1, "no (fixed fee)"),
    ("TF-100k", 5, 5, 1, "no (fixed fee)"),
    ("TF-1m", 0.5, 0.5, 1, "no (fixed fee)"),
    ("LOAD-max", 575, 0, 1, "no (asymmetric)"),
    ("LOAD-bp", 250, 0, 1, "no (asymmetric)"),
    ("CDSC-1y", 0, 100, 1, "no (asymmetric)"),
    ("REDFEE", 0, 200, 1, "no (asymmetric)"),
]
HORIZONS = [1, 4, 12, 20]
ALPHA_REFS = [("alpha 0.5%/yr", 0.005 / 4), ("alpha 1%/yr", 0.01 / 4), ("alpha 2%/yr", 0.02 / 4)]
SAMPLES = [("1926Q3-2025Q2", "1926Q3", "2025Q2"), ("1963Q3-2025Q2", "1963Q3", "2025Q2"),
           ("2000Q1-2025Q2", "2000Q1", "2025Q2")]
PRIMARY = "1963Q3-2025Q2"
DELTA_LOADING = 0.1


def fetch() -> tuple[bytes, str]:
    CACHE.mkdir(exist_ok=True)
    f = CACHE / "F-F_Research_Data_Factors_CSV_2025-07cut.zip"
    if not f.exists():
        url = BASE + urllib.parse.quote(PINNED)
        req = urllib.request.Request(url, headers={"User-Agent": "etfport-lab research"})
        f.write_bytes(urllib.request.urlopen(req, timeout=60).read())
    raw = f.read_bytes()
    return raw, hashlib.sha256(raw).hexdigest()


def monthly(raw: bytes) -> tuple[pd.DataFrame, str]:
    with zipfile.ZipFile(io.BytesIO(raw)) as z:
        text = z.read(z.namelist()[0]).decode("latin-1")
    lines = text.splitlines()
    header = next(l.strip() for l in lines if "CRSP database" in l)
    rows = []
    started = False
    for l in lines:
        s = l.strip()
        if s.startswith(",Mkt-RF"):
            if started:
                break          # a second header begins the annual block
            started = True
            continue
        if started:
            parts = [p.strip() for p in s.split(",")]
            if len(parts) == 5 and len(parts[0]) == 6 and parts[0].isdigit():
                rows.append([parts[0]] + [float(p) / 100 for p in parts[1:]])
            elif rows:
                break
    df = pd.DataFrame(rows, columns=["ym", "MktRF", "SMB", "HML", "RF"])
    df.index = pd.PeriodIndex(pd.to_datetime(df.pop("ym"), format="%Y%m"), freq="M")
    return df, header


def quarterly(m: pd.DataFrame) -> pd.DataFrame:
    q = m.index.asfreq("Q")
    g = m.groupby(q)
    n = g.size()
    out = pd.DataFrame({
        "MktRF": g.apply(lambda d: (1 + d.MktRF + d.RF).prod() - (1 + d.RF).prod()),
        "SMB": g.apply(lambda d: (1 + d.SMB).prod() - 1),
        "HML": g.apply(lambda d: (1 + d.HML).prod() - 1),
    })
    return out[n == 3]


def stats(q: pd.DataFrame) -> dict:
    res = {}
    for name, a, b in SAMPLES:
        s = q.loc[pd.Period(a, "Q"):pd.Period(b, "Q")]
        res[name] = {c: (len(s), s[c].mean(), s[c].std(ddof=1), s[c].std(ddof=1) / math.sqrt(len(s)))
                     for c in ["MktRF", "SMB", "HML"]}
    return res


def sig3(x: float) -> str:
    return f"{x:.3g}"


def classify(r: float) -> str:
    return "negligible" if r < 0.05 else ("material" if r >= 0.2 else "intermediate")


def main() -> None:
    raw, sha = fetch()
    m, header = monthly(raw)
    q = quarterly(m)
    st = stats(q)
    print(f"Input: {PINNED}\nSHA-256: {sha}\nVintage header: {header}")
    print(f"Monthly rows: {len(m)} ({m.index[0]} to {m.index[-1]}); complete quarters: {len(q)}\n")

    print("### Factor statistics (percent per quarter; SE = SD/sqrt(N), independent quarters assumed)\n")
    print("| Sample | Factor | N | Mean | SD | SE |\n|---|---|---|---|---|---|")
    for name, _, _ in SAMPLES:
        for c in ["MktRF", "SMB", "HML"]:
            n, mu, sd, se = st[name][c]
            print(f"| {name} | {c} | {n} | {100*mu:.3f} | {100*sd:.3f} | {100*se:.3f} |")

    refs = list(ALPHA_REFS)
    for c in ["SMB", "HML"]:
        refs.append((f"0.1 x {c} ({PRIMARY})", DELTA_LOADING * st[PRIMARY][c][1]))
    for name, _, _ in SAMPLES:
        if name != PRIMARY:
            for c in ["SMB", "HML"]:
                refs.append((f"0.1 x {c} ({name})", DELTA_LOADING * st[name][c][1]))

    print("\n### Reference gains (bp per quarter)\n")
    print("| Reference | Gain (bp/quarter) | Source |\n|---|---|---|")
    for r, g in refs:
        print(f"| {r} | {g/BP:.2f} | {'assumed' if r.startswith('alpha') else 'French library, pinned cut'} |")

    print("\n### Switching costs (bp per unit switched) and M1 break-even quarterly gain\n")
    print("| Case | In M1 | in: entry = break-even | in: round trip | out: entry = break-even | out: round trip |")
    print("|---|---|---|---|---|---|")
    rows = []
    for name, ab, as_, e, inm1 in CASES:
        in_entry, in_exit = e + ab, as_ + e
        out_entry, out_exit = as_ + e, e + ab
        rows.append((name, inm1, in_entry, in_exit, out_entry, out_exit))
        print(f"| {name} | {inm1} | {in_entry:g} | {in_entry+in_exit:g} | {out_entry:g} | {out_entry+out_exit:g} |")

    print("\n### Materiality ratio R = break-even / reference gain (primary references), and class\n")
    prim = [r for r in refs if r[0].startswith("alpha") or PRIMARY in r[0]]
    print("| Case | Switch | " + " | ".join(r for r, _ in prim) + " | Class |")
    print("|---|---|" + "---|" * len(prim) + "---|")
    classes = {}
    for name, inm1, ie, _, oe, _ in rows:
        for sw, be in (("in", ie), ("out", oe)):
            cells, rs = [], []
            for _, g in prim:
                if g <= 0:
                    cells.append("undefined (reference gain <= 0)")
                else:
                    r = be * BP / g
                    rs.append(r)
                    cells.append(sig3(r))
            worst = classify(max(rs)) if rs else "undefined"
            best = classify(min(rs)) if rs else "undefined"
            cls = worst if worst == best else f"{best} to {worst}"
            classes[(name, sw)] = (min(rs), max(rs))
            print(f"| {name} | {sw} | " + " | ".join(cells) + f" | {cls} |")

    print("\n### Sensitivity: ratio range over exposure references from the other samples\n")
    other = [r for r in refs if not (r[0].startswith("alpha") or PRIMARY in r[0])]
    print("| Case | Switch | " + " | ".join(r for r, _ in other) + " |")
    print("|---|---|" + "---|" * len(other))
    for name, inm1, ie, _, oe, _ in rows:
        for sw, be in (("in", ie), ("out", oe)):
            cells = ["undefined (reference gain <= 0)" if g <= 0 else sig3(be * BP / g) for _, g in other]
            print(f"| {name} | {sw} | " + " | ".join(cells) + " |")

    print("\n### Yardstick outside M1: round trip amortized over H quarters, as annualized bp (x4)\n")
    print("| Case | Switch | " + " | ".join(f"H={h}" for h in HORIZONS) + " |")
    print("|---|---|" + "---|" * len(HORIZONS))
    for name, inm1, ie, ix, oe, ox in rows:
        for sw, rt in (("in", ie + ix), ("out", oe + ox)):
            print(f"| {name} | {sw} | " + " | ".join(f"{4*rt/h:.3g}" for h in HORIZONS) + " |")

    print("\n### Hypothesis H\n")
    a_max = max(classes[("NTF-liquid", "in")][1], classes[("NTF-liquid", "out")][1])
    print(f"(a) NTF-liquid largest ratio = {sig3(a_max)}: {'holds' if a_max < 0.05 else 'FAILS'}")
    kinds = {"front load": ["LOAD-max", "LOAD-bp"], "transaction-fee platform, small trade": ["TF-10k"],
             "stressed or niche ETF": ["NTF-niche", "ETF-stress"]}
    for k, cs in kinds.items():
        mx = max(max(classes[(c, "in")][1], classes[(c, "out")][1]) for c in cs)
        print(f"(b) {k}: largest ratio = {sig3(mx)}: {'material somewhere' if mx >= 0.2 else 'FAILS'}")


if __name__ == "__main__":
    main()
