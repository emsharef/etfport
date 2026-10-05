"""D26 preparation: the larger menu's scenario count and the reproducible limit (LAB_REQUEST_3: 'If the existing scenario
representation prevents that scale, report the precise limitation and the largest reproducible case').
Each case runs in its own process with a time limit; it records the tree's states, the joint program's size, solver status
and iterations, the time to build the tree and to solve the dynamic program and the plan (policy 2), the myopic policy's
per-state solves, the peak memory, and a feasibility check (the dynamic program's cash at every node >= -1e-8).
Menus: N funds, M ETFs, K factors; nonnegative loadings and rates drawn with default_rng(26); M9 with mild persistence.
Run: uv run python experiments/d26-prep/scale.py [--quick]
"""
import json
import multiprocessing as mp
import platform
import resource
import subprocess
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "d16-harness")); sys.path.insert(0, str(HERE))


def menu(N, M, K, law, seed=26):
    from harness_n import mn_model
    rng = np.random.default_rng([seed, N, M, K])
    BE = np.eye(K)[:M] if M <= K else np.vstack([np.eye(K), rng.uniform(0, 1, (M - K, K))])
    BE = BE + np.where(BE == 0, rng.uniform(0, 0.3, BE.shape), 0)
    BA = rng.uniform(0, 1, (N, K)); BA[:, 0] += 0.5
    d = K + N
    return mn_model(BA=BA, BE=BE, lam=np.linspace(0.015, 0.005, K), alpha=rng.uniform(-0.002, 0.003, N), premium_sd=np.full(K, 0.005),
                    sigma_f=np.linspace(0.08, 0.04, K), sigma_A=rng.uniform(0.015, 0.03, N), alpha_sd=rng.uniform(0.002, 0.004, N),
                    sigma_E=np.full(M, 0.002), cE=np.full(M, 0.0003), gamma=5.0,
                    kp=np.concatenate([rng.uniform(0.002, 0.006, N), np.full(M, 0.0003)]), km=np.concatenate([rng.uniform(0.002, 0.006, N), np.full(M, 0.0003)]),
                    cap=np.concatenate([np.full(N, 0.1), np.full(M, np.inf)]), phi=np.full(d, 0.9), q=np.full(d, 1e-7), law=law, observe_factor=True)


def case(N, M, K, law):
    import policies as P
    t0 = time.time(); Mo = menu(N, M, K, law); nodes = Mo.tree(2)[1]; t_tree = time.time() - t0
    x0 = np.zeros(Mo.n); h0 = 1.0
    t0 = time.time(); D = Mo.solve(x0, h0); t_dyn = time.time() - t0; st = dict(Mo.last_stats)
    feas = min(min(D["h"][1]), D["h"][0][0])
    t0 = time.time(); Mo.solve(x0, h0, budget_t={0}); t_plan = time.time() - t0
    mu0, S0 = Mo.moments(0, Mo.m0); t0 = time.time(); xmy, _, hmy = Mo.one_review(mu0, S0, x0, h0); P.tomorrow(Mo, nodes, xmy, hmy); t_my = time.time() - t0
    return dict(N=N, M=M, K=K, law=law, states=len(nodes), n_vars=st["n_vars"], status=st["status"], iters=st["iters"], t_tree=t_tree, t_dyn=t_dyn,
                t_dyn_solver=st["solve_time"], t_plan=t_plan, t_myopic=t_my, min_cash=feas, maxrss_mb=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2 ** 20)


def main():
    quick = "--quick" in sys.argv; limit = 60 if quick else 1800
    grid = [(3, 2, 2, "product"), (4, 2, 2, "product"), (5, 2, 2, "product"), (6, 2, 2, "product"),
            (3, 2, 2, "axis"), (5, 2, 2, "axis"), (10, 3, 2, "axis"), (20, 3, 3, "axis"), (30, 4, 3, "axis"), (40, 4, 3, "axis"), (60, 5, 4, "axis")]
    out = []
    for N, M, K, law in grid:
        if quick and N > 10:
            continue
        cmd = [sys.executable, "-c", f"import sys,json; sys.path.insert(0,{str(HERE)!r}); import scale; print('RESULT'+json.dumps(scale.case({N},{M},{K},{law!r})))"]
        t0 = time.time()
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=limit)
            line = [l for l in r.stdout.splitlines() if l.startswith("RESULT")]
            rec = json.loads(line[0][6:]) if line else dict(N=N, M=M, K=K, law=law, error=(r.stderr.strip().splitlines() or ["no output"])[-1][:300])
        except subprocess.TimeoutExpired:
            rec = dict(N=N, M=M, K=K, law=law, error=f"timeout after {limit} s")
        rec["wall"] = time.time() - t0; out.append(rec); print(json.dumps(rec), flush=True)
    env = dict(machine=platform.machine(), processor="Apple M2 Pro (10 cores), 32 GB", python=platform.python_version(),
               numpy=np.__version__, cvxpy=__import__("cvxpy").__version__, clarabel=__import__("clarabel").__version__)
    json.dump(dict(cases=out, env=env, time_limit_s=limit), open(HERE / "scale.json", "w"), indent=1)


if __name__ == "__main__":
    main()
