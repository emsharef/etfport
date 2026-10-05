"""Red's reproduction of experiment 021 (ROADMAP reading, Deviation 1), written from the registered Design
without reading run.py, model.py, riccati.py or griddp.py.

Quadratic costs (Q1-Q3): red's own exact backward recursion. The value function is a quadratic form in
z = (x_{t-1}, m_t, 1); each stage maximizes over x in closed form; the expectation over m_{t+1} = m_t + xi,
xi ~ N(0, Q_t), adds trace terms only (m is a martingale). Predictive mean mu = B m_lambda + (m_alpha, -c^E),
predictive covariance S_t = B Sigma_f B' + D + G P_t G' with G = [B, fund selector]; Kalman updates from
public factor returns (premia) and fund residuals (alphas).
Proportional costs (P1): red's own grid DP with a separable L1 distance transform and 20-point
Gauss-Hermite expectation with linear interpolation in the belief mean.

Usage: uv run python experiments/021/red_reproduce.py [Q|P]
"""
import sys
import numpy as np

LAM = np.array([0.0184, 0.00897]); SDF = np.array([0.0854, 0.06095]); SEL = np.array([0.0054, 0.0039])
AM, AS = -0.0019, 0.0035                       # pooled alpha prior mean and SD per quarter
FUNDS = [np.array([1.0, 0.3]), np.array([1.0, 0.0]), np.array([0.9, 0.5])]
ETFS = [np.array([1.0, 0.0]), np.array([0.0, 1.0])]
SDA, SDE, CE = 0.02, 0.002, 0.0001
LF, LE = 0.1, 0.01


def instance(name):
    if name == "Q1":
        nf, ne, K, unc_l = 1, 1, 1, False
    elif name == "Q2":
        nf, ne, K, unc_l = 2, 1, 1, True
    else:
        nf, ne, K, unc_l = 3, 2, 2, True
    B = np.array([f[:K] for f in FUNDS[:nf]] + [e[:K] for e in ETFS[:ne]])
    n = nf + ne
    D = np.diag([SDA ** 2] * nf + [SDE ** 2] * ne)
    Sf = np.diag(SDF[:K] ** 2)
    Lam = np.diag([LF] * nf + [LE] * ne)
    # belief state m = (alphas, premia if uncertain); P diag blocks
    Pa = np.eye(nf) * AS ** 2
    Pl = np.diag(SEL[:K] ** 2) if unc_l else np.zeros((K, K))
    return dict(nf=nf, ne=ne, K=K, B=B, D=D, Sf=Sf, Lam=Lam, Pa=Pa, Pl=Pl, unc_l=unc_l, n=n)


def solve(I, gamma, T):
    nf, K, n, B = I["nf"], I["K"], I["n"], I["B"]
    Da = I["D"][:nf, :nf]
    ul = I["unc_l"]
    dm = nf + (K if ul else 0)
    # posterior covariances P_t (t = 0..T) and innovation covariances Q_t = P_t - P_{t+1}
    Pa, Pl = [I["Pa"]], [I["Pl"]]
    for t in range(T):
        Pa.append(np.linalg.inv(np.linalg.inv(Pa[-1]) + np.linalg.inv(Da)))
        Pl.append(np.linalg.inv(np.linalg.inv(Pl[-1]) + np.linalg.inv(I["Sf"])) if ul else Pl[-1])
    Gsel = np.zeros((n, nf)); Gsel[:nf, :nf] = np.eye(nf)
    def S(t):
        return B @ I["Sf"] @ B.T + I["D"] + Gsel @ Pa[t] @ Gsel.T + B @ Pl[t] @ B.T
    # mu = Mm m + mu0
    Mm = np.zeros((n, dm)); Mm[:nf, :nf] = np.eye(nf)
    if ul:
        Mm[:, nf:] = B
    mu0 = np.zeros(n); mu0[nf:] = -CE
    if not ul:
        mu0 += B @ LAM[:K]
    def Q(t):
        q = np.zeros((dm, dm)); q[:nf, :nf] = Pa[t] - Pa[t + 1]
        if ul:
            q[nf:, nf:] = Pl[t] - Pl[t + 1]
        return q
    # V_{t}(x_-, m) = z' H z / 2 with z = (x_-, m, 1)  (H symmetric)
    dz = n + dm + 1
    H = np.zeros((dz, dz))              # V_T = 0
    pol = [None] * T
    Lam = I["Lam"]
    for t in reversed(range(T)):
        # E V_{t+1}(x, m'): z' = (x, m + xi, 1): E[z'Hz'] = z_det' H z_det + tr(H_mm Q_t)
        Hx = H[:n, :n]; Hxm = H[:n, n:n + dm]; Hx1 = H[:n, -1]
        Hmm = H[n:n + dm, n:n + dm]; Hm1 = H[n:n + dm, -1]; H11 = H[-1, -1]
        c_extra = np.trace(Hmm @ Q(t))
        # stage objective in (x, x_-, m, 1): x'(Mm m + mu0) - g/2 x'S x - 1/2 (x - x_-)'Lam(x - x_-) + E V
        St = S(t)
        # write total as 1/2 w' Wm w, w = (x, x_-, m, 1)
        dw = 2 * n + dm + 1
        W = np.zeros((dw, dw))
        ix, iy, im, i1 = slice(0, n), slice(n, 2 * n), slice(2 * n, 2 * n + dm), 2 * n + dm
        W[ix, ix] += -gamma * St - Lam + Hx
        W[ix, iy] += Lam; W[iy, ix] += Lam
        W[iy, iy] += -Lam
        W[ix, im] += Mm + Hxm; W[im, ix] += (Mm + Hxm).T
        W[ix, i1] += mu0 + Hx1; W[i1, ix] += mu0 + Hx1
        W[im, im] += Hmm; W[im, i1] += Hm1; W[i1, im] += Hm1
        W[i1, i1] += H11 + c_extra
        # maximize over x: x* = -Wxx^{-1} Wx,rest r
        Wxx = W[ix, ix]; Wxr = W[ix, n:]
        Kfull = -np.linalg.solve(Wxx, Wxr)             # x* = Kfull @ r, r = (x_-, m, 1)
        pol[t] = dict(Kx=Kfull[:, :n], Lm=Kfull[:, n:n + dm], l=Kfull[:, -1], S=St, Mm=Mm, mu0=mu0)
        # FOC residual check
        r = np.random.default_rng(t).normal(size=dw - n)
        xs = Kfull @ r
        foc = Wxx @ xs + Wxr @ r
        pol[t]["foc"] = float(np.max(np.abs(foc)))
        Wrr = W[n:, n:]
        H = Wrr - Wxr.T @ np.linalg.solve(Wxx, Wxr)
    m0 = np.concatenate([np.full(nf, AM), LAM[:K]]) if ul else np.full(nf, AM)
    return pol, H, m0, dm


def report_q():
    worst = 0.0
    print("| instance | gamma | T | speed t=0 (funds; ETFs) | speed t=T-1 | aim t=0 funds | aim ETFs | alpha part (funds; ETFs) | value 0 / incumbent (bp/q) |")
    for name in ("Q1", "Q2", "Q3"):
        I = instance(name)
        for g in (2, 5, 10):
            for T in (4, 8):
                pol, H, m0, dm = solve(I, g, T)
                worst = max(worst, max(p["foc"] for p in pol))
                n, nf = I["n"], I["nf"]
                sp0 = np.diag(np.eye(n) - pol[0]["Kx"]); spT = np.diag(np.eye(n) - pol[-1]["Kx"])
                IK = np.eye(n) - pol[0]["Kx"]
                aim = np.linalg.solve(IK, pol[0]["Lm"] @ m0 + pol[0]["l"])
                # alpha part: response to the alpha means only
                ma = np.zeros(dm); ma[:nf] = m0[:nf]
                aim_a = np.linalg.solve(IK, pol[0]["Lm"] @ ma)
                def val(x):
                    z = np.concatenate([x, m0, [1.0]]); return 0.5 * z @ H @ z / T * 1e4
                inc = np.array([0.3 / nf] * nf + [0.3 / I['ne']] * I['ne'])   # 0.3 in funds and 0.3 in ETFs, split equally
                f = lambda v: ",".join(f"{x:.3f}" for x in v)
                print(f"| {name} | {g} | {T} | {f(sp0[:nf])}; {f(sp0[nf:])} | {f(spT[:nf])}; {f(spT[nf:])} | {f(aim[:nf])} | {f(aim[nf:])} | "
                      f"{f(aim_a[:nf])}; {f(aim_a[nf:])} | {val(np.zeros(n)):.2f} / {val(inc):.2f} |")
    print(f"largest FOC residual {worst:.1e}")


# ---------------------------------------------------------------- proportional costs, P1 grid DP
def dt1d(v, k, h):
    """max_y v(y) - k |x - y| on a grid of step h (exact on the grid)."""
    out = v.copy()
    for i in range(1, len(v)):
        out[i] = max(out[i], out[i - 1] - k * h)
    for i in range(len(v) - 2, -1, -1):
        out[i] = max(out[i], out[i + 1] - k * h)
    return out


def p1(gamma, T, h, kf=0.01, ke=0.0005):
    B = np.array([1.0, 1.0]); n = int(round(1 / h)) + 1; xs = np.linspace(0, 1, n)
    Sf = SDF[0] ** 2; D = np.diag([SDA ** 2, SDE ** 2])
    Pa = [AS ** 2]
    for t in range(T):
        Pa.append(1 / (1 / Pa[-1] + 1 / SDA ** 2))
    sd = np.sqrt(AS ** 2 - Pa[T])              # sd of m_t - m_0 at the horizon (grid half-width uses 4 sd)
    mg = AM + np.linspace(-4, 4, 41) * max(sd, 1e-12)
    gh_x, gh_w = np.polynomial.hermite_e.hermegauss(20); gh_w = gh_w / gh_w.sum()
    X1, X2 = np.meshgrid(xs, xs, indexing="ij")
    V = np.zeros((41, n, n))               # V_{t+1}(x_-, m)
    for t in reversed(range(T)):
        S = Sf * np.outer(B, B) + D + np.diag([Pa[t], 0.0])
        q = np.sqrt(Pa[t] - Pa[t + 1])
        Vn = np.zeros_like(V)
        # E V_{t+1}(x, m') by Gauss-Hermite with linear interpolation in m (clamped)
        for j, m in enumerate(mg):
            EV = np.zeros((n, n))
            for z, w in zip(gh_x, gh_w):
                mp = np.clip(m + q * z, mg[0], mg[-1])
                k = min(np.searchsorted(mg, mp) - 1, 39); k = max(k, 0)
                a = (mp - mg[k]) / (mg[k + 1] - mg[k])
                EV += w * ((1 - a) * V[k] + a * V[k + 1])
            mu = np.array([LAM[0] + m, LAM[0] - CE])
            Wt = mu[0] * X1 + mu[1] * X2 - gamma / 2 * (S[0, 0] * X1 ** 2 + 2 * S[0, 1] * X1 * X2 + S[1, 1] * X2 ** 2) + EV
            A = np.apply_along_axis(dt1d, 1, Wt, ke, h)      # over ETF coordinate
            Vn[j] = np.apply_along_axis(dt1d, 0, A, kf, h)   # over fund coordinate
        V = Vn
    j0 = 20
    i03 = int(round(0.3 / h))
    return V[j0, 0, 0] / T * 1e4, V[j0, i03, i03] / T * 1e4


def p1_bands(gamma, T, h, kf=0.01, ke=0.0005):
    """Fund and ETF no-trade widths per (t, m) where the instrument's own frictionless target is interior,
    the other instrument held at its target (Deviation 2's reading)."""
    B = np.array([1.0, 1.0]); n = int(round(1 / h)) + 1; xs = np.linspace(0, 1, n)
    Sf = SDF[0] ** 2; D = np.diag([SDA ** 2, SDE ** 2])
    Pa = [AS ** 2]
    for t in range(T):
        Pa.append(1 / (1 / Pa[-1] + 1 / SDA ** 2))
    sd = np.sqrt(AS ** 2 - Pa[T])
    mg = AM + np.linspace(-4, 4, 41) * sd
    gh_x, gh_w = np.polynomial.hermite_e.hermegauss(20); gh_w = gh_w / gh_w.sum()
    X1, X2 = np.meshgrid(xs, xs, indexing="ij")
    V = np.zeros((41, n, n)); fw, ew = [], []
    for t in reversed(range(T)):
        S = Sf * np.outer(B, B) + D + np.diag([Pa[t], 0.0])
        q = np.sqrt(Pa[t] - Pa[t + 1])
        Vn = np.zeros_like(V)
        for j, m in enumerate(mg):
            EV = np.zeros((n, n))
            for z, w in zip(gh_x, gh_w):
                mp = np.clip(m + q * z, mg[0], mg[-1])
                k = max(min(np.searchsorted(mg, mp) - 1, 39), 0)
                a = (mp - mg[k]) / (mg[k + 1] - mg[k])
                EV += w * ((1 - a) * V[k] + a * V[k + 1])
            mu = np.array([LAM[0] + m, LAM[0] - CE])
            one = mu[0] * X1 + mu[1] * X2 - gamma / 2 * (S[0, 0] * X1 ** 2 + 2 * S[0, 1] * X1 * X2 + S[1, 1] * X2 ** 2)
            Wt = one + EV
            A = np.apply_along_axis(dt1d, 1, Wt, ke, h)
            Vn[j] = np.apply_along_axis(dt1d, 0, A, kf, h)
            # frictionless target: argmax of the one-period score on the grid (future value is flat in x when costs are zero)
            it = np.unravel_index(np.argmax(one), one.shape)
            # fund band: ETF incoming at its target; for each incoming fund f_, optimal fund choice
            if 0 < it[0] < n - 1:
                ecol = it[1]
                Af = np.max(Wt - ke * h * np.abs(np.arange(n)[None, :] - ecol), axis=1)     # best over ETF choice, per fund choice
                cost = kf * h * np.abs(np.arange(n)[:, None] - np.arange(n)[None, :])         # [choice, incoming]
                best = np.argmax(Af[:, None] - cost, axis=0)
                nt = np.where(best == np.arange(n))[0]
                fw.append((nt.max() - nt.min()) * h if len(nt) else 0.0)
            if 0 < it[1] < n - 1:
                frow = it[0]
                Ae = np.max(Wt - kf * h * np.abs(np.arange(n)[:, None] - frow), axis=0)
                cost = ke * h * np.abs(np.arange(n)[:, None] - np.arange(n)[None, :])
                best = np.argmax(Ae[:, None] - cost, axis=0)
                nt = np.where(best == np.arange(n))[0]
                ew.append((nt.max() - nt.min()) * h if len(nt) else 0.0)
        V = Vn
    return np.array(fw), np.array(ew)


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "B":
    for g, T in ((5, 4), (10, 4), (2, 4)):
        fw, ew = p1_bands(g, T, 1 / 200)
        print(f"P1 bands gamma {g} T {T} h 1/200: fund points {len(fw)} median {np.median(fw):.3f} [{fw.min():.3f}, {fw.max():.3f}]; "
              f"ETF points {len(ew)} median {np.median(ew):.3f} [{ew.min():.3f}, {ew.max():.3f}]")
    sys.exit(0)


if __name__ == "__main__":
    w = sys.argv[1] if len(sys.argv) > 1 else "QP"
    if "Q" in w:
        report_q()
    if "P" in w:
        for g, T in ((5, 4), (2, 4), (10, 4)):
            for h in (1 / 100, 1 / 200):
                v0, vi = p1(g, T, h)
                print(f"P1 gamma {g} T {T} h 1/{int(round(1 / h))}: value from 0 {v0:.2f}, from incumbent {vi:.2f} bp/q")
