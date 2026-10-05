"""Experiment 053 (D21): claim 047's reserve rule as a policy (part 3(b); 5b6373ae) against the dynamic optimum and the
repeated one-review policy. Registered design: experiments/053-d21-reserve-rule-comparison.md.
Run: uv run python experiments/053/run.py
"""
import importlib.util
import itertools
import json
import multiprocessing as mp
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "d16-harness"))
from harness import m8_model  # noqa: E402

_p = importlib.util.spec_from_file_location("presets", HERE.parent / "presets.py"); PR = importlib.util.module_from_spec(_p); _p.loader.exec_module(PR)
_e = importlib.util.spec_from_file_location("run047", HERE.parent / "047" / "run.py"); E47 = importlib.util.module_from_spec(_e); _e.loader.exec_module(E47)
_q = importlib.util.spec_from_file_location("run052", HERE.parent / "052" / "run.py"); E52 = importlib.util.module_from_spec(_q); _q.loader.exec_module(E52)
TOLX = 1e-7
SETTINGS = [("preset", 1.0), ("revision_var", 0.25), ("revision_var", 4.0), ("fund_buy", 0.5), ("fund_buy", 2.0), ("etf_sell", 0.5), ("etf_sell", 2.0)]


def model(regime, setting, mult):
    P = PR.PRESETS[regime]
    pa = P["alpha_sd"] ** 2; s2 = P["sigma_A"] ** 2; V = pa ** 2 / (pa + s2) * (mult if setting == "revision_var" else 1.0)
    return m8_model(bA=1.0, bE=1.0, cE=P["etf_fee"], lam=P["premium"][0], alpha=P["alpha_mean"], premium_sd=P["premium_sd"][0], alpha_revision_var=V,
                    sigma_f=P["factor_sd"][0], sigma_A=P["sigma_A"], gamma=P["gamma"], beta=1.0,
                    etf_rate_buy=P["etf_rate"], etf_rate_sell=P["etf_rate"] * (mult if setting == "etf_sell" else 1.0),
                    fund_rate_buy=P["fund_rate"] * (mult if setting == "fund_buy" else 1.0), fund_rate_sell=P["fund_rate"], fund_rate=P["fund_rate"],
                    capA=P["fund_cap"], observe_factor=False)


def cost(M, u):
    return float(M.kAp * max(u[0], 0) + M.kAm * max(-u[0], 0) + M.kEp * max(u[1], 0) + M.kEm * max(-u[1], 0))


def score(M, mu, S, x, xm):
    return float(mu @ x - 0.5 * M.gamma * x @ S @ x - cost(M, x - xm))


def cash_after(M, h0, x, xm):
    return float(h0 - np.sum(x - xm) - cost(M, x - xm))


def tomorrow(M, nodes, x0, h0p):
    xs, es = [], []
    for nd in nodes:
        mu, S = M.moments(1, nd["m"]); xx, ee, _ = E47.one_review(M, mu, S, x0 * nd["g"], max(h0p, 0.0)); xs.append(xx); es.append(ee)
    return xs, es


def value(M, nodes, x0m, x0, xs):
    mu0, S0 = M.moments(0, M.m0); v = score(M, mu0, S0, x0, x0m)
    for k, nd in enumerate(nodes):
        mu, S = M.moments(1, nd["m"]); v += M.beta * nd["prob"] * score(M, mu, S, xs[k], x0 * nd["g"])
    return v


def rule_root(M, nodes, x0m, h0, xmy, hmy):
    """Claim 047 part 3(b)'s rule: p^rule = p^my + S_E/(gamma Sigma_0EE), S_E from the myopic tomorrow; fund at a^my."""
    mu0, S0 = M.moments(0, M.m0)
    xs, es = tomorrow(M, nodes, xmy, hmy)
    t = []
    for k, nd in enumerate(nodes):
        mu, S = M.moments(1, nd["m"]); g1 = (mu - M.gamma * S @ xs[k])[1]; u = xs[k][1] - xmy[1] * nd["g"][1]
        if u > TOLX:
            t.append(M.kEp)
        elif u < -TOLX:
            t.append(-M.kEm)
        elif xs[k][1] > TOLX:
            t.append(g1)
        else:
            t.append(max(g1, -M.kEm))
    q = np.array([nd["prob"] for nd in nodes]); G = np.array([nd["g"][1] for nd in nodes])
    SE = float(M.beta * q @ (G * np.array(t)))
    target = np.array([xmy[0], max(xmy[1] + SE / (M.gamma * S0[1, 1]), 0.0)])
    if cash_after(M, h0, target, x0m) >= 0:
        return target, SE, False
    lo, hi = 0.0, 1.0                                     # move toward p^my until the budget is met
    for _ in range(60):
        mid = 0.5 * (lo + hi); x = xmy + mid * (target - xmy)
        if cash_after(M, h0, x, x0m) >= 0:
            lo = mid
        else:
            hi = mid
    return xmy + lo * (target - xmy), SE, True


def S_E_at(M, nodes, x, h):
    """S_E = beta E[g_E t_{1,E}] from the one-review tomorrow at root holdings x with cash h (the registered slope convention)."""
    xs, _ = tomorrow(M, nodes, x, h); t = []
    for k, nd in enumerate(nodes):
        mu, S = M.moments(1, nd["m"]); g1 = (mu - M.gamma * S @ xs[k])[1]; u = xs[k][1] - x[1] * nd["g"][1]
        t.append(M.kEp if u > TOLX else (-M.kEm if u < -TOLX else (g1 if xs[k][1] > TOLX else max(g1, -M.kEm))))
    q = np.array([nd["prob"] for nd in nodes]); G = np.array([nd["g"][1] for nd in nodes])
    return float(M.beta * q @ (G * np.array(t)))


def rule_variant(M, nodes, x0m, h0, xmy, gate, fixed_point):
    """Deviation 1 (post hoc, labelled; not the registered rule): the rule with one or both of two changes.
    gate: apply the shift only when the myopic root trades the ETF (part 3(b)'s same-direction case; an ETF held
    untraded today has t^my inside its band, which absorbs S_E in part 3(b)'s exact display).
    fixed_point: evaluate S_E at the rule's own root and cash (damped iteration) instead of at the myopic root.
    The fund stays at a^my and the result is clipped to feasibility as in the registered rule."""
    mu0, S0 = M.moments(0, M.m0)
    if gate and abs(xmy[1] - x0m[1]) <= TOLX:
        return xmy.copy(), 0.0, 0
    p = xmy[1]; SE = 0.0; it = 0
    for it in range(1, 61 if fixed_point else 2):
        x = np.array([xmy[0], max(p, 0.0)]); h = cash_after(M, h0, x, x0m)
        if h < 0:
            break
        SE = S_E_at(M, nodes, x, h); pn = xmy[1] + SE / (M.gamma * S0[1, 1])
        if not fixed_point or abs(pn - p) < 1e-8:
            p = pn; break
        p = 0.5 * p + 0.5 * pn
    target = np.array([xmy[0], max(p, 0.0)])
    if cash_after(M, h0, target, x0m) >= 0:
        return target, SE, it
    lo, hi = 0.0, 1.0
    for _ in range(60):
        mid = 0.5 * (lo + hi); x = xmy + mid * (target - xmy)
        if cash_after(M, h0, x, x0m) >= 0:
            lo = mid
        else:
            hi = mid
    return xmy + lo * (target - xmy), SE, it


def rule_band(M, nodes, x0m, h0, xmy):
    """Deviation 1, fourth variant (post hoc, labelled): part 3(b)'s exact display used as the rule. With the fund at
    a^my, the ETF solves today's line g_{0,E}(p) + S_E = t_{0,E}(p), t_{0,E} = kappa^+ if bought, -kappa^- if sold,
    inside the band if held (so p^fix - p^my = [S_E - (t^fix - t^my)]/(gamma Sigma_0EE)), with S_E at the rule's own
    point (damped iteration); then the zero bound and the budget clip toward p^my as in the registered rule."""
    mu0, S0 = M.moments(0, M.m0); gS = M.gamma * S0[1, 1]; base = mu0[1] - M.gamma * S0[1, 0] * xmy[0]

    def line(SE):
        pb, ps = (base + SE - M.kEp) / gS, (base + SE + M.kEm) / gS
        return max(pb if pb > x0m[1] else (ps if ps < x0m[1] else x0m[1]), 0.0)
    p = line(0.0); SE = 0.0; it = 0
    for it in range(1, 61):
        x = np.array([xmy[0], p]); h = cash_after(M, h0, x, x0m)
        if h < 0:
            break
        SE = S_E_at(M, nodes, x, h); pn = line(SE)
        if abs(pn - p) < 1e-8:
            p = pn; break
        p = 0.5 * p + 0.5 * pn
    target = np.array([xmy[0], p])
    if cash_after(M, h0, target, x0m) >= 0:
        return target, SE, it
    lo, hi = 0.0, 1.0
    for _ in range(60):
        mid = 0.5 * (lo + hi); x = xmy + mid * (target - xmy)
        if cash_after(M, h0, x, x0m) >= 0:
            lo = mid
        else:
            hi = mid
    return xmy + lo * (target - xmy), SE, it


VARIANTS = {"gate": (True, False), "fixed_point": (False, True), "gate_fixed_point": (True, True), "band": (None, None)}


def math_fields(M, x0m, h0, D, xmy, hmy):
    """Deviation 4 (math's note 2026-09-30-d19-reserve-rule, per cell): h^my, N(x^my_0), the no-reserve check, the capacity
    F = h + (1 - kappa^-_E) g^min_E p and Res = F(x^dyn) - F(x^my), and Pi_E's sign at the myopic root (experiment 052's
    part 3(a) computation: the multiplier LP's range, defined where the ETF trades today and h^my > 0)."""
    nodes = D["levels"][1]; xd = D["x"][0][0]; hd = cash_after(M, h0, xd, x0m)
    gmin = min(nd["g"][1] for nd in nodes); F = lambda x, h: float(h + (1 - M.kEm) * gmin * x[1])
    Nm = max(p["need"] for p in E52.need_parts(M, nodes, xmy))
    pi = None
    t0 = E52.slope_today(M, xmy, x0m, 1, None)
    if hmy > E52.HS and xmy[1] > TOLX and t0 is not None:
        x1my, h1my = [], []
        for nd in nodes:
            mu, S = M.moments(1, nd["m"]); xx, _, hh = E47.one_review(M, mu, S, xmy * nd["g"], hmy); x1my.append(xx); h1my.append(hh)
        Lm = E52.R49.LP(M, x0m, xmy, hmy, nodes, x1my, h1my, root=False)
        rng = E52.ranges(Lm, Lm.S(1) - M.beta * (1 + t0) * Lm.Eeta1())
        if None not in rng:
            pi = "+" if rng[0] > 1e-9 else ("-" if rng[1] < -1e-9 else ("0" if max(map(abs, rng)) <= 1e-9 else "either"))
    return dict(h_my=float(hmy), N_my=float(Nm), no_reserve_check=bool(hmy > 0 and hmy >= Nm), F_dyn=F(xd, hd), F_my=F(xmy, hmy),
                Res=F(xd, hd) - F(xmy, hmy), Pi_E_sign_at_my=pi)


def cell(args):
    regime, start, cash, (setting, mult) = args
    M = model(regime, setting, mult); x0m = np.array(start, float)
    D = M.solve(x0m, cash, T=2); nodes = D["levels"][1]; xd = D["x"][0][0]
    mu0, S0 = M.moments(0, M.m0); xmy, emy, hmy = E47.one_review(M, mu0, S0, x0m, cash)
    xs_my, _ = tomorrow(M, nodes, xmy, hmy); v_my = value(M, nodes, x0m, xmy, xs_my)
    xr, SE, clipped = rule_root(M, nodes, x0m, cash, xmy, hmy); hr = cash_after(M, cash, xr, x0m)
    xs_r, _ = tomorrow(M, nodes, xr, hr); v_r = value(M, nodes, x0m, xr, xs_r)
    hd = cash_after(M, cash, xd, x0m)
    Lmy0 = 1e4 * (D["value"] - v_my); variants = {}
    for name, (gate, fp) in VARIANTS.items():
        xv, SEv, itv = rule_band(M, nodes, x0m, cash, xmy) if name == "band" else rule_variant(M, nodes, x0m, cash, xmy, gate, fp); hv = cash_after(M, cash, xv, x0m)
        xs_v, _ = tomorrow(M, nodes, xv, hv); Lv = 1e4 * (D["value"] - value(M, nodes, x0m, xv, xs_v))
        variants[name] = dict(x=xv.tolist(), S_E=SEv, iters=itv, reserve=[float(xv[1] - xmy[1]), float(hv - hmy)], loss_bp=Lv,
                              recovery=(1 - Lv / Lmy0) if Lmy0 > 0.01 else None)
    Lmy, Lr = 1e4 * (D["value"] - v_my), 1e4 * (D["value"] - v_r)
    return dict(regime=regime, start=list(start), cash=cash, setting=setting, mult=mult, fund_buy=M.kAp, etf_sell=M.kEm,
                V_alpha=float(M.P(0)[1, 1] - M.P(1)[1, 1]), x_dyn=xd.tolist(), x_my=xmy.tolist(), x_rule=xr.tolist(), S_E=SE, rule_clipped=clipped,
                reserve_dyn=[float(xd[1] - xmy[1]), float(hd - hmy)], reserve_rule=[float(xr[1] - xmy[1]), float(hr - hmy)],
                loss_my_bp=Lmy, loss_rule_bp=Lr, recovery=(1 - Lr / Lmy) if Lmy > 0.01 else None,
                dyn_binds=bool(D["h"][0][0] < 1e-6 or min(D["h"][1]) < 1e-6),
                math=math_fields(M, x0m, cash, D, xmy, hmy),
                myopic_trades_etf=bool(abs(xmy[1] - x0m[1]) > TOLX), deviation1=variants)


def main():
    cells = list(itertools.product(("equity-style", "fixed-income-style"), ((0.0, 0.9), (0.15, 0.0), (0.075, 0.45)), (1.0, 0.005), SETTINGS))
    with mp.Pool(8) as pool:
        res = pool.map(cell, cells, chunksize=2)
    json.dump(dict(cells=res, statement="claim 047 at 5b6373ae (part 3(b)'s rule); unchanged in part 3(b) at a9875d4e",
                   deviation1="post hoc variants of the rule, labelled; the registered rule is x_rule"), open(HERE / "summary.json", "w"), indent=0,
              default=lambda o: o.tolist() if hasattr(o, "tolist") else float(o))
    print("done", len(res))


if __name__ == "__main__":
    main()
