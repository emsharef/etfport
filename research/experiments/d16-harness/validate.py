"""Validation of the D16/D18 harness (not an experiment; no findings). Run: uv run python experiments/d16-harness/validate.py
1. One review left (T = 1): the harness equals experiment 045's joint solver for one fund and one ETF and claim 110's
   two-scalar reduction (an independent implementation), at random instances with fees, ETF rates and binding budgets.
2. Claim 107 part 3 (T = 2): with a frictionless, fee-free, residual-free ETF, a slack budget and ETF bounds that do not
   bind, the fund's holding at every node equals the reduced fund-only program's.
3. Myopia check (T = 2): with no trading costs, a slack budget and no learning (a degenerate parameter law), the dynamic
   root decision equals the one-review decision (the benchmark `mossin1968optimal` names for serially independent returns).
"""
import importlib.util
import json
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from harness import Model  # noqa: E402

_s = importlib.util.spec_from_file_location("run045", HERE.parent / "045" / "run.py")
m45 = importlib.util.module_from_spec(_s); _s.loader.exec_module(m45)


def check1(n=60):
    rng = np.random.default_rng([2016, 1]); out = []
    for i in range(n):
        bA = rng.uniform(0.3, 1.5); lam = rng.uniform(-0.01, 0.03); al = rng.uniform(-0.01, 0.01)
        sl, sa = rng.uniform(0.001, 0.01), rng.uniform(0.0005, 0.004)          # parameter spreads
        sf, sA, sE = 0.08, 0.02 * np.sqrt(1 + rng.uniform(0.01, 3)), (rng.uniform(0.005, 0.02) if i % 3 == 0 else 0.0)
        kp, km = rng.uniform(0, 0.02, 2); kEp, kEm = rng.uniform(0, 0.005, 2); cE = rng.uniform(0, 0.002)
        M = Model(bA=bA, kAp=kp, kAm=km, kEp=kEp, kEm=kEm, capA=rng.choice([0.25, 1.0]), cE=cE,
                  theta_atoms=[(lam + a * sl, al + b * sa) for a in (1, -1) for b in (1, -1)], theta_probs=[0.25] * 4,
                  z_atoms=[(a * sf, b * sA, c * sE) for a in (1, -1) for b in (1, -1) for c in (1, -1)], z_probs=[0.125] * 8)
        x0 = np.array([rng.uniform(0, 1) * M.capA, 0.0 if rng.random() < 0.5 else rng.uniform(0, 0.5)])
        mu, S = M.moments(0, M.m0)
        # 045's parametrization: r = bA (b_E = 1), sigma_EE = S_EE - sE^2, v = S_AA - bA^2 sigma_EE, alpha~ = mu_A - r mu_E
        sEE = S[1, 1] - sE ** 2; v = S[0, 0] - bA ** 2 * sEE
        assert abs(S[0, 1] - bA * sEE) < 1e-15
        o = m45.One(r=np.array([bA]), mu=mu[1], sEE=sEE, at=np.array([mu[0] - bA * mu[1]]), v=np.array([v]), kp=np.array([kp]),
                    km=np.array([km]), cap=np.array([M.capA]), xm=np.array([x0[0]]), kEp=kEp, kEm=kEm, pm=x0[1], sE=sE ** 2, h=None)
        xf, pf, _ = o.joint(); need = float(xf[0] - x0[0] + pf - x0[1] + o.cost(xf, pf)); o.h = max(need * rng.uniform(0.3, 1.5), 1e-3)
        xj, pj, _ = o.joint(); red, _ = o.reduce()
        H = M.solve(x0, o.h, T=1)["x"][0][0]
        out.append(dict(i=i, dj=float(max(abs(H[0] - xj[0]), abs(H[1] - pj))), dr=float(max(abs(H[0] - red["x"][0]), abs(H[1] - red["p"]))),
                        binding=bool(o.k(np.array([H[0]]), H[1]) < 1e-7), sE=sE))
    return out


def check2():
    out = []
    for lam, al, a0s in ((0.02, 0.003, (0.0, 0.1, 0.25)), (0.03, -0.002, (0.0, 0.15)), (0.025, 0.0, (0.05, 0.2))):
        M = Model(bA=1.0, kAp=0.005, kAm=0.005, kEp=0.0, kEm=0.0, cE=0.0, capA=0.25,
                  theta_atoms=[(lam + a * 0.005, al + b * 0.002) for a in (1, -1) for b in (1, -1)], theta_probs=[0.25] * 4,
                  z_atoms=[(a * 0.08, b * 0.02, 0.0) for a in (1, -1) for b in (1, -1)], z_probs=[0.25] * 4)
        for a0 in a0s:
            for p0 in (0.0, 0.5):
                full = M.solve(np.array([a0, p0]), 100.0, T=2)
                red = M.reduced_fund(a0, T=2)
                d = max(abs(full["x"][t][k][0] - red[t][k]) for t in range(2) for k in range(len(red[t])))
                pmin = min(full["x"][t][k][1] for t in range(2) for k in range(len(red[t])))
                out.append(dict(lam=lam, al=al, a0=a0, p0=p0, diff=float(d), etf_min=float(pmin), nodes=len(red[1])))
    return out


def check3():
    out = []
    for lam, al in ((0.02, 0.003), (0.01, -0.004)):
        M = Model(bA=1.0, kAp=0.0, kAm=0.0, kEp=0.0, kEm=0.0, cE=0.0, capA=0.25, theta_atoms=[(lam, al)], theta_probs=[1.0])
        for x0 in ((0.0, 0.0), (0.2, 0.3)):
            dyn = M.solve(np.array(x0), 100.0, T=2)["x"][0][0]; my = M.myopic_root(np.array(x0), 100.0)
            out.append(dict(lam=lam, al=al, x0=x0, diff=float(np.max(np.abs(dyn - my)))))
    return out


def main():
    c1, c2, c3 = check1(), check2(), check3()
    S = dict(check1=c1, check2=c2, check3=c3)
    json.dump(S, open(HERE / "validation.json", "w"), indent=0, default=float)
    print(f"1. T = 1 against 045's joint solver: largest holding difference {max(r['dj'] for r in c1):.1e}; against claim 110's reduction "
          f"{max(r['dr'] for r in c1):.1e} ({len(c1)} instances, {sum(r['binding'] for r in c1)} with a binding budget, {sum(r['sE'] > 0 for r in c1)} with ETF residual risk)")
    print(f"2. claim 107 part 3 at T = 2: largest fund-holding difference over all nodes {max(r['diff'] for r in c2):.1e} ({len(c2)} instances; "
          f"smallest ETF holding {min(r['etf_min'] for r in c2):.3f}, so the zero bound is slack)")
    print(f"3. no costs, slack budget, no learning: dynamic root against one-review root {max(r['diff'] for r in c3):.1e} ({len(c3)} instances)")


if __name__ == "__main__":
    main()
