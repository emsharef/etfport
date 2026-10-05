"""Red's independent reproduction of experiment 023 Part B (generic M6 target, one instrument).
Written from the Design only. Exact DP on (holdings grid, target lattice state); unmarked holdings, beta = 1."""
import numpy as np, itertools, sys

GAMMA, SIG2 = 5.0, 0.0854 ** 2
C = GAMMA * SIG2
LAWS = {'symmetric': [(+1.0, 0.5), (-1.0, 0.5)], 'skewed': [(+3.0, 0.2), (-0.75, 0.8)]}
COSTS = {'5/5': (5e-4, 5e-4), '100/0': (100e-4, 0.0)}


def cell(law, costs, r, T, cap):
    kp, km = COSTS[costs]
    w = (kp + km) / C
    h = w / 200
    s = r * w
    steps = LAWS[law]
    x0 = 100 * w
    mx = max(abs(d) for d, _ in steps) * s
    lo_g, hi_g = x0 - (T * mx + 2 * w), x0 + (T * mx + 2 * w)
    grid = x0 + h * np.arange(int(np.floor((lo_g - x0) / h)), int(np.ceil((hi_g - x0) / h)) + 1)
    capv = x0 + 0.5 * w if cap else np.inf
    grid = grid[grid <= capv + 1e-12]
    n = len(grid)
    # lattice states at t: tuple of counts per step type -> target
    def states(t):
        return [c for c in itertools.product(range(t + 1), repeat=len(steps)) if sum(c) == t]
    def target(cnt):
        return x0 + s * sum(k * d for k, (d, _) in zip(cnt, steps))
    V = {}   # V[t+1][state] value as function of holding carried in
    bands = {}
    for t in range(T - 1, -1, -1):
        Vt = {}
        for st in states(t):
            xs = target(st)
            W = -0.5 * C * (grid - xs) ** 2
            if t < T - 1:
                for j, (d, p) in enumerate(steps):
                    nxt = tuple(st[i] + (i == j) for i in range(len(steps)))
                    W = W + p * V[nxt]
            f1 = W - kp * grid; f2 = W + km * grid
            m1 = f1.max(); m2 = f2.max()
            i1 = np.flatnonzero(f1 >= m1 - 1e-15 * max(1, abs(m1)))[0]      # no-trade tie-break: widest band
            i2 = np.flatnonzero(f2 >= m2 - 1e-15 * max(1, abs(m2)))[-1]
            lo, hi = grid[i1], grid[i2]
            Vn = np.where(grid < lo, W[i1] - kp * (lo - grid), np.where(grid > hi, W[i2] - km * (grid - hi), W))
            Vt[st] = Vn
            interior = 0 < i1 and i2 < n - 1 and hi < capv - 1e-12
            bands[(t, st)] = (lo, hi, xs, interior)
        V = Vt
    return dict(bands=bands, w=w, h=h, s=s, kp=kp, km=km, steps=steps, T=T, states=states)


def check(res):
    b, w, h, kp, km, steps, T = res['bands'], res['w'], res['h'], res['kp'], res['km'], res['steps'], res['T']
    U = sum(p for d, p in steps if d > 0); D = 1 - U
    tau = (kp * U - km * D) / C
    maxw, lasterr, coarseerr, fine = 0, 0, 0, []
    e1 = [0, 0, 0]   # (bands tested, holds, fails)
    nint = 0
    for (t, st), (lo, hi, xs, inn) in b.items():
        if not inn:
            continue
        nint += 1
        maxw = max(maxw, (hi - lo) / w)
        if t == T - 1:
            lasterr = max(lasterr, abs(lo - (xs - kp / C)) / h, abs(hi - (xs + km / C)) / h)
            continue
        coarse = all(abs(d) * res['s'] > 2 * w for d, _ in steps)
        if coarse:
            coarseerr = max(coarseerr, abs(lo - (xs - kp / C + tau)) / h, abs(hi - (xs + km / C + tau)) / h)
        else:
            fine.append((hi - lo) / w)
        nxt = [tuple(st[i] + (i == j) for i in range(len(steps))) for j in range(len(steps))]
        nb = [b[(t + 1, q)] for q in nxt]
        if all(q[3] for q in nb):
            e1[0] += 1
            straddle = any(not (hi <= q[0] + h * 1.0001 or lo >= q[1] - h * 1.0001) for q in nb)
            full = abs((hi - lo) - w) <= h * 1.0001
            if full == (not straddle):
                e1[1] += 1
            else:
                e1[2] += 1
    return dict(nint=nint, maxw=maxw, lasterr=lasterr, coarseerr=coarseerr, fine=fine, e1=e1, coarse=all(abs(d) * res['s'] > 2 * w for d, _ in steps))


if __name__ == '__main__':
    tot = [0, 0, 0]; viol = 0; rows = []
    for law, costs, r, T, cap in itertools.product(LAWS, COSTS, [0.25, 0.5, 1, 2, 4], [4, 8, 20], [False, True]):
        res = cell(law, costs, r, T, cap); ck = check(res)
        for i in range(3): tot[i] += ck['e1'][i]
        v = (ck['maxw'] > 1 + 2 * res['h'] / res['w'] + 1e-9) + (ck['lasterr'] > 1.0001) + (ck['coarse'] and ck['coarseerr'] > 1.0001)
        viol += v
        b0 = res['bands'][(0, tuple([0] * len(LAWS[law])))]
        fs = ck['fine']
        rows.append((law, costs, r, T, cap, ck['nint'], ck['maxw'], ck['lasterr'], ck['coarseerr'] if ck['coarse'] else None,
                     (min(fs), float(np.median(fs))) if fs else None, (b0[1] - b0[0]) / res['w']))
        print(law, costs, r, T, 'cap' if cap else 'none', 'nint', ck['nint'], 'maxw %.4f' % ck['maxw'], 'last %.2fh' % ck['lasterr'],
              'coarse %.2fh' % ck['coarseerr'] if ck['coarse'] else '-', 'fine min/med %.3f/%.3f' % (min(fs), np.median(fs)) if fs else '-',
              't0 width %.3f' % ((b0[1] - b0[0]) / res['w']), flush=True)
    print('violations', viol, '1e: tested %d holds %d fails %d' % tuple(tot))
    cs = C
    print('cube-root ratios (t=0, symmetric, no cap, T=20):')
    for costs in COSTS:
        kp, km = COSTS[costs]
        for r in [0.25, 0.5, 1, 2]:
            row = [x for x in rows if x[0] == 'symmetric' and x[1] == costs and x[2] == r and x[3] == 20 and not x[4]][0]
            w = (kp + km) / C; s = r * w
            print(costs, r, 'width/static %.3f' % row[10], 'ratio %.3f' % (row[10] * w / (s ** (2 / 3) * (kp + km) ** (1 / 3) / C ** (1 / 3))))
