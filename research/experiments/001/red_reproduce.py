"""Red's independent reproduction of experiment 001, written from the Design without reading run.py.

Usage: uv run python experiments/001/red_reproduce.py
Downloads the pinned French 3-factor file to a temporary directory (never committed), checks its SHA-256
against the one reported in Results, and recomputes Parts C-E and the factor statistics.
"""
import csv
import hashlib
import io
import math
import tempfile
import urllib.request
import zipfile
from fractions import Fraction as F
from pathlib import Path

URL = ("https://mba.tuck.dartmouth.edu/pages/faculty/ken.french/Data_Library/Historical_Archives/"
       "08%202025%20Update/ftp/F-F_Research_Data_Factors_CSV.zip")
SHA = "b70e34975273b2bb267236fc59679a3252cbae3dc4c8bec8d44ea14a3d9ce17e"

raw = urllib.request.urlopen(URL, timeout=60).read()
assert hashlib.sha256(raw).hexdigest() == SHA, "pinned file changed"
text = zipfile.ZipFile(io.BytesIO(raw)).read("F-F_Research_Data_Factors.csv").decode("latin-1")
print("vintage:", text.splitlines()[0].strip())

# Monthly block: rows with a 6-digit yyyymm key, up to the first blank line after the header.
rows = []
for line in text.splitlines()[4:]:
    parts = [p.strip() for p in line.split(",")]
    if len(parts) != 5 or not (parts[0].isdigit() and len(parts[0]) == 6):
        if rows:
            break
        continue
    rows.append((int(parts[0]), *[float(p) / 100 for p in parts[1:]]))
print("monthly rows:", len(rows), rows[0][0], "to", rows[-1][0])

# Complete calendar quarters.
by_q = {}
for ym, mkt, smb, hml, rf in rows:
    y, m = divmod(ym, 100)
    by_q.setdefault((y, (m - 1) // 3 + 1), []).append((mkt, smb, hml, rf))
quarters = {}
for key, ms in sorted(by_q.items()):
    if len(ms) != 3:
        continue
    prod = lambda xs: math.prod(1 + x for x in xs)
    quarters[key] = {
        "MktRF": prod(m + r for m, _, _, r in ms) - prod(r for *_, r in ms),
        "SMB": prod(s for _, s, _, _ in ms) - 1,
        "HML": prod(h for _, _, h, _ in ms) - 1,
    }
print("complete quarters:", len(quarters))

samples = {"1926Q3-2025Q2": ((1926, 3), (2025, 2)), "1963Q3-2025Q2": ((1963, 3), (2025, 2)),
           "2000Q1-2025Q2": ((2000, 1), (2025, 2))}
stats = {}
print("\n| Sample | Factor | N | Mean % | SD % | SE % |")
for name, (lo, hi) in samples.items():
    for fac in ("MktRF", "SMB", "HML"):
        xs = [v[fac] for k, v in quarters.items() if lo <= k <= hi]
        n = len(xs)
        mean = sum(xs) / n
        sd = math.sqrt(sum((x - mean) ** 2 for x in xs) / (n - 1))
        stats[name, fac] = (n, mean, sd, sd / math.sqrt(n))
        print(f"| {name} | {fac} | {n} | {100*mean:.3f} | {100*sd:.3f} | {100*sd/math.sqrt(n):.3f} |")

# Part B cases, bp, exact: (kA_b, kA_s, kE)
bp = lambda x: F(x)
cases = {"Z": (0, 0, 0), "EQ5": (5, 5, 5), "EQ25": (25, 25, 25), "NTF-liquid": (0, 0, 1),
         "NTF-niche": (0, 0, 25), "ETF-stress": (0, 0, 100), "TF-10k": (50, 50, 1),
         "TF-100k": (5, 5, 1), "TF-1m": (F(1, 2), F(1, 2), 1), "LOAD-max": (575, 0, 1),
         "LOAD-bp": (250, 0, 1), "CDSC-1y": (0, 100, 1), "REDFEE": (0, 200, 1)}
# Fixed-fee cases: $50 on the stated size.
assert F(50, 10_000) * 10_000 == 50 and F(50, 100_000) * 10_000 == 5 and F(50, 1_000_000) * 10_000 == F(1, 2)

refs = {"a0.5": F(125, 10), "a1": F(25), "a2": F(50)}
for name in samples:
    for fac in ("SMB", "HML"):
        refs[f"0.1x{fac} {name}"] = F(0.1 * stats[name, fac][1] * 10_000)   # bp per quarter

def cls(r):
    return "negligible" if r < F(5, 100) else ("material" if r >= F(2, 10) else "intermediate")

primary = ["a0.5", "a1", "a2", "0.1xSMB 1963Q3-2025Q2", "0.1xHML 1963Q3-2025Q2"]
print("\nprimary refs (bp/q):", {k: round(float(refs[k]), 2) for k in primary})
print("\n| Case | Switch | entry | round trip | ratios (primary) | classes | amortized x4, H=1,4,12,20 |")
largest = {}
for c, (ab, as_, e) in cases.items():
    for sw in ("in", "out"):
        entry, exit_ = (e + ab, as_ + e) if sw == "in" else (as_ + e, e + ab)
        rt = entry + exit_
        ratios = [F(entry) / refs[k] for k in primary]
        classes = sorted({cls(r) for r in ratios})
        am = [float(F(rt) * 4 / H) for H in (1, 4, 12, 20)]
        largest[c, sw] = max(ratios)
        print(f"| {c} | {sw} | {float(entry):g} | {float(rt):g} | "
              f"{', '.join(f'{float(r):.3g}' for r in ratios)} | {'/'.join(classes)} | "
              f"{', '.join(f'{x:.3g}' for x in am)} |")

print("\nsensitivity (other samples):")
for c, (ab, as_, e) in cases.items():
    for sw in ("in", "out"):
        entry = (e + ab) if sw == "in" else (as_ + e)
        other = [k for k in refs if k.startswith("0.1x") and "1963" not in k]
        print(c, sw, [f"{float(F(entry) / refs[k]):.3g}" for k in other])

print("\nH(a) NTF-liquid max ratio:", f"{float(largest['NTF-liquid', 'in']):.3g}",
      "FAILS" if largest["NTF-liquid", "in"] >= F(5, 100) else "holds")
for kind, cs in {"front load": ["LOAD-max", "LOAD-bp"], "TF small trade": ["TF-10k"],
                 "stressed/niche ETF": ["NTF-niche", "ETF-stress"]}.items():
    m = max(largest[c, s] for c in cs for s in ("in", "out"))
    print(f"H(b) {kind}: max ratio {float(m):.3g}", "material somewhere" if m >= F(2, 10) else "FAILS")
