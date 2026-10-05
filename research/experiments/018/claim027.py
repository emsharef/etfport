"""Experiment 018, Deviation 1: claim 027's fibre-confined two-stage procedure on the zero-cost cells, exactly.

Claim 027 (math): stage 1 b* = argmax G over b(F); stage 2 maximizes H over the fibre {w in F : b(w) = b*};
T = G(b*) + V(b*) = max {Qbar_0(w) : w in F, b(w) = b*}; loss J - T, with the identity
    J - T = [V(b_J) - V(b*)] - [G(b*) - G(b_J)].
With zero rates, caps 1 and budget 1, b(F) = conv{0, loading rows}, which is 018's stage-1 set, so b* is 018's
target. Cost-bearing cells are not computed here (there b(F) differs from 018's set). The fibre maximum is
experiment 020's exact routine (`fibre_max`: the fibre is a point with one ETF and a segment with two).

Run: uv run python experiments/018/claim027.py
"""
import importlib.util
import json
import statistics
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent


def _load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


e018 = _load("e018c", HERE / "run.py")
e020 = _load("e020c", HERE.parent / "020" / "run.py")


def main():
    rows = [r for r in json.load(open(HERE / "results.json")) if r["cost"] == "Z"]
    bp = lambda x: float(x) * 1e4  # noqa: E731
    out = []
    for r in rows:
        I = e018.instance(r["geom"], r["cost"], Fr(r["alpha"]), Fr(r["gamma"]), Fr(r["sA"]), r["start"])
        J = Fr(r["VF"])
        bstar = tuple(Fr(x) for x in r["bstar"])
        bJ = e018.expo(I, [Fr(x) for x in r["wJ"]])
        T = e020.fibre_max(I, bstar)
        assert T is not None
        G = lambda b: e018.g1(b, I.gamma)  # noqa: E731
        Vs, VJ = T - G(bstar), J - G(bJ)
        loss = J - T
        resid_gain, factor_cost = VJ - Vs, G(bstar) - G(bJ)
        assert loss == resid_gain - factor_cost and factor_cost >= 0 and loss >= 0
        mism = sum(e018.SF[k] ** 2 * (bJ[k] - bstar[k]) ** 2 for k in range(2))
        out.append(dict(r=r, loss=loss, soft=Fr(r["2S-alpha"]["gap"]), gain=resid_gain, cost=factor_cost, mism=mism))
    n = len(out)
    L = [bp(o["loss"]) for o in out]
    print(f"zero-rate cells {n}; b_TB outside b(F) in {sum(o['r']['stage1_binding'] for o in out)}")
    print(f"claim-027 loss J - T: exactly 0 in {sum(o['loss'] == 0 for o in out)}; < 1 bp {sum(x < 1 for x in L)}; "
          f">= 1 bp {sum(x >= 1 for x in L)}; median {statistics.median(L):.3f} bp; max {max(L):.3f} bp")
    d = [bp(o["loss"] - o["soft"]) for o in out]
    print(f"claim-027 loss minus 018's soft-target gap: min {min(d):+.3f}, median {statistics.median(d):+.3f}, max {max(d):+.3f} bp; "
          f"equal in {sum(o['loss'] == o['soft'] for o in out)}; confined worse in {sum(o['loss'] > o['soft'] for o in out)}")
    print(f"identity terms (median, max): residual-stage gain V(b_J) - V(b*) {statistics.median([bp(o['gain']) for o in out]):.3f}, "
          f"{max(bp(o['gain']) for o in out):.3f}; factor-stage cost G(b*) - G(b_J) {statistics.median([bp(o['cost']) for o in out]):.3f}, "
          f"{max(bp(o['cost']) for o in out):.3f}; mismatch ||b_J - b*||_Sf median {statistics.median([float(o['mism']) ** 0.5 for o in out]):.4f}, "
          f"max {max(float(o['mism']) ** 0.5 for o in out):.4f}")
    for key in ("geom", "alpha", "gamma", "start"):
        print(f"by {key}: " + "; ".join(
            f"{v}: zero {sum(1 for o in out if o['r'][key] == v and o['loss'] == 0)}/{sum(1 for o in out if o['r'][key] == v)}, "
            f"max {max(bp(o['loss']) for o in out if o['r'][key] == v):.2f}" for v in sorted({o['r'][key] for o in out}, key=str)))


if __name__ == "__main__":
    main()
