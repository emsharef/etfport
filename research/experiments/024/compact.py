"""Experiment 024: compact the raw run outputs (main/h8/sens/prop .json, tens of MB, not committed) into summary.json:
per-path certainty equivalents per policy, and path-averaged holdings statistics. Everything report.py prints comes
from summary.json. Run: uv run python experiments/024/compact.py
"""
import json
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent


def squeeze(rows):
    pols = list(rows[0][1].keys())
    ce = {p: [r[1][p] for r in rows] for p in pols}
    ex = {}
    for p in pols:
        e = [r[2][p] for r in rows]
        ex[p] = dict(zero_funds=np.mean([x["zero_funds"] for x in e], axis=0).tolist(),
                     zero_etfs=np.mean([x["zero_etfs"] for x in e], axis=0).tolist(),
                     inaction_funds=float(np.mean([x["inaction_funds"] for x in e])),
                     inaction_etfs=float(np.mean([x["inaction_etfs"] for x in e])),
                     invested=float(np.mean([x["invested"] for x in e])),
                     budget_binding=float(np.mean([x["budget_binding"] for x in e])))
        if e[0].get("half_f") is not None:
            hf = np.concatenate([x["half_f"] for x in e]); he = np.concatenate([x["half_e"] for x in e])
            ex[p]["half_band"] = dict(funds_p90=float(np.percentile(hf, 90)), funds_median=float(np.median(hf)), funds_n=int(len(hf)),
                                      etfs_p90=float(np.percentile(he, 90)), etfs_median=float(np.median(he)), etfs_n=int(len(he)))
    return dict(ce=ce, extras=ex)


def main():
    out = {}
    for part in ("main", "h8", "sens", "prop"):
        d = json.load(open(HERE / f"{part}.json"))
        out[part] = dict(seconds=d["seconds"], data=({k: squeeze(v) for k, v in d["rows"].items()} if part == "sens" else squeeze(d["rows"])))
    (HERE / "summary.json").write_text(json.dumps(out))
    print("wrote summary.json")


if __name__ == "__main__":
    main()
