"""Experiment 022 Parts 1-2 (and sensitivities): simulation of M5's optimal policy and the baselines under common
random numbers. Registered design: experiments/022-m5-realistic-value.md.

Run:    uv run python experiments/022/run.py            (writes experiments/022/results.json)
        uv run python experiments/022/stationary.py     (Part 3; writes experiments/022/stationary.json)
Report: uv run python experiments/022/report.py
"""
import json
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import model  # noqa: E402

POLICIES = ["D12", "myopic", "static", "ETF-only", "two-stage", "equal", "no-trade", "oracle"]


def draw_truth(I, R, rngs):
    lam = np.stack([rg.multivariate_normal(I.lam_hat, I.P0L) for rg in rngs])
    alpha = np.stack([rg.choice(model.BSW[0], size=I.N, p=model.BSW[1]) for rg in rngs])
    return lam, alpha


def simulate(I, R, policies, seed0=2022):
    rngs = [np.random.default_rng([seed0, r]) for r in range(R)]
    lam_t, alp_t = draw_truth(I, R, rngs)
    theta = np.hstack([alp_t, lam_t])                                  # (R, d)
    mu_true = theta @ I.G.T + I.g0                                      # (R, n)
    Lf = np.linalg.cholesky(I.Sf)
    zf = np.stack([rg.standard_normal((I.T, I.K)) for rg in rngs]) @ Lf.T          # (R, T, K)
    zA = np.stack([rg.standard_normal((I.T, I.N)) for rg in rngs]) * I.sdA        # (R, T, N)
    # beliefs (shared by every policy)
    m = np.tile(I.m0, (R, 1)); ms = []
    for t in range(I.T):
        ms.append(m.copy())
        f = lam_t + zf[:, t]
        yA = alp_t + zA[:, t]                                           # r^A - B^A f
        mA = m[:, :I.N] + (yA - m[:, :I.N]) @ I.KA[t].T
        mL = m[:, I.N:] + (f - m[:, I.N:]) @ I.KL[t].T
        m = np.hstack([mA, mL])
    n, N = I.n, I.N
    Eall = np.eye(n); Eetf = Eall[:, N:]
    Ks = {}
    if "D12" in policies:
        Ks["D12"] = (Eall, model.riccati(I, Eall, I.S, I.Q, I.T))
    if "static" in policies:
        Ks["static"] = (Eall, model.riccati(I, Eall, lambda t: I.S(0), I.Q, I.T))
    if "ETF-only" in policies:
        Ks["ETF-only"] = (Eetf, model.riccati(I, Eetf, I.S, I.Q, I.T))
    if "oracle" in policies:
        Ks["oracle"] = (Eall, model.riccati(I, Eall, lambda t: I.Sigma_r, lambda t: np.zeros((N + I.K, N + I.K)), I.T))
    Lam = np.diag(I.Lam)
    out = {}
    extra = {}
    for p in policies:
        x_prev = np.tile(I.x_inc, (R, 1))
        ce = np.zeros(R)
        turn_A = turn_E = 0.0
        fund_ret = np.zeros(R); fund_short = np.zeros(R); nshort = 0
        acap = np.zeros(R); acap_short = np.zeros(R); gross = np.zeros(R)   # Deviation 1(a)
        for t in range(I.T):
            mt = theta if p == "oracle" else ms[t]
            if p in Ks:
                E, K = Ks[p]
                s = np.hstack([x_prev, mt, np.ones((R, 1))])
                x = x_prev + (s @ K[t].T) @ E.T
            elif p == "myopic":
                A = I.gamma * I.Sigma_r + Lam
                x = np.linalg.solve(A, (mt @ I.G.T + I.g0 + x_prev @ Lam).T).T
            elif p == "two-stage":
                St = I.S(t)
                PL = I.PL[t]
                bstar = np.linalg.solve(I.gamma * (I.Sf + PL), mt[:, N:].T).T          # (R, K)
                KKT = np.block([[I.gamma * St + Lam, I.B], [I.B.T, np.zeros((I.K, I.K))]])
                rhs = np.hstack([mt @ I.G.T + I.g0 + x_prev @ Lam, bstar])
                x = np.linalg.solve(KKT, rhs.T).T[:, :n]
            elif p == "equal":
                x = np.full((R, n), 1.0 / n)
            elif p == "no-trade":
                x = x_prev.copy()
            u = x - x_prev
            ce += np.einsum("ri,ri->r", x, mu_true) - 0.5 * I.gamma * np.einsum("ri,ij,rj->r", x, I.Sigma_r, x) \
                - 0.5 * np.einsum("ri,i,ri->r", u, I.Lam, u)
            turn_A += np.abs(u[:, :N]).sum(1).mean(); turn_E += np.abs(u[:, N:]).sum(1).mean()
            fr = x[:, :N] * mu_true[:, :N]
            fund_ret += fr.sum(1); fund_short += np.where(x[:, :N] < 0, fr, 0).sum(1); nshort += (x[:, :N] < 0).sum()
            ac = x[:, :N] * alp_t
            acap += ac.sum(1); acap_short += np.where(x[:, :N] < 0, ac, 0).sum(1); gross += np.abs(x).sum(1)
            x_prev = x
        out[p] = ce / I.T
        extra[p] = dict(turnover_funds=turn_A / I.T, turnover_etfs=turn_E / I.T, fund_expected_return=float(fund_ret.mean() / I.T),
                        fund_short_expected_return=float(fund_short.mean() / I.T), share_short_fund_positions=nshort / (R * I.T * N),
                        alpha_capture_bp=float(acap.mean() / I.T * 1e4), alpha_capture_short_bp=float(acap_short.mean() / I.T * 1e4),
                        gross_leverage=float(gross.mean() / I.T))
    split = split_stats(I, Ks["D12"][1], ms) if "D12" in Ks else None
    return out, extra, split


def split_stats(I, K, ms):
    """Trading speeds per block and the aim's exposure and alpha parts (M5's definition) on realized beliefs."""
    n, N, d = I.n, I.N, I.N + I.K
    res = {}
    for t in (0, 20, I.T - 1):
        Kx = np.eye(n) + K[t][:, :n]
        speed = np.diag(np.eye(n) - Kx)
        Km, k0 = K[t][:, n:n + d], K[t][:, n + d]
        inv = np.linalg.inv(np.eye(n) - Kx)
        m = ms[t]
        aim = (m @ Km.T + k0) @ inv.T
        mX = m.copy(); mX[:, :N] = I.m0[:N]
        aimX = (mX @ Km.T + k0) @ inv.T
        aimA = aim - aimX
        g = lambda a, blk: float(np.abs(a[:, blk]).sum(1).mean())  # noqa: E731
        fb, eb = slice(0, N), slice(N, n)
        res[t] = dict(speed_funds=float(speed[:N].mean()), speed_etfs=float(speed[N:].mean()),
                      aim_gross_funds=g(aim, fb), aim_gross_etfs=g(aim, eb),
                      exposure_part_gross_funds=g(aimX, fb), exposure_part_gross_etfs=g(aimX, eb),
                      alpha_part_gross_funds=g(aimA, fb), alpha_part_gross_etfs=g(aimA, eb),
                      aim_net_funds=float(aim[:, fb].sum(1).mean()), aim_net_etfs=float(aim[:, eb].sum(1).mean()))
    return res


def summarize(out):
    res = {}
    for p, v in out.items():
        res[p] = dict(mean_bp=float(v.mean() * 1e4), se_bp=float(v.std(ddof=1) / np.sqrt(len(v)) * 1e4))
    pairs = {}
    for b in out:
        if b != "D12" and "D12" in out:
            d = out["D12"] - out[b]
            pairs[f"D12 - {b}"] = dict(mean_bp=float(d.mean() * 1e4), se_bp=float(d.std(ddof=1) / np.sqrt(len(d)) * 1e4))
        if b != "oracle" and "oracle" in out:
            d = out["oracle"] - out[b]
            pairs[f"oracle - {b}"] = dict(mean_bp=float(d.mean() * 1e4), se_bp=float(d.std(ddof=1) / np.sqrt(len(d)) * 1e4))
    return res, pairs


def main():
    t0 = time.time()
    I = model.Inst()
    calib = dict(lam_hat=I.lam_hat.tolist(), Sf=I.Sf.tolist(), n_quarters=I.nq, BA=I.BA.tolist(), sdA=I.sdA.tolist())
    R = 5000
    out, extra, split = simulate(I, R, POLICIES)
    res, pairs = summarize(out)
    extra_R = 0
    while max(v["se_bp"] for k, v in pairs.items()) > 0.1 and extra_R < 20000:     # registered: raise R by 5,000
        extra_R += 5000
        o2, _, _ = simulate(I, R + extra_R, POLICIES)
        res, pairs = summarize(o2)
    sens = {}
    for lab, kw in (("gamma 2", dict(gamma=2.0)), ("gamma 10", dict(gamma=10.0)), ("lambda_A 0.5", dict(lamA=0.5))):
        J = model.Inst(**kw)
        o, _, _ = simulate(J, 2000, ["D12", "ETF-only", "two-stage", "oracle"])
        sens[lab] = summarize(o)
    json.dump(dict(calibration=calib, R=R + extra_R, main=res, pairs=pairs, extra=extra,
                   split={str(k): v for k, v in split.items()}, sensitivities={k: dict(main=v[0], pairs=v[1]) for k, v in sens.items()},
                   seconds=time.time() - t0), open(HERE / "results.json", "w"), indent=1)
    print(f"R = {R + extra_R}; seconds {time.time() - t0:.0f}")


if __name__ == "__main__":
    main()
