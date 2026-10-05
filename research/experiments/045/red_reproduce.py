"""Red's reproduction of experiment 045 (claims 110 and 111), written without reading run.py or report.py. It runs red's
own implementations from its claim 110 and 111 reviews (red110.rule; red111.fibre) and its experiment 044 generator (argument
1: a directory holding red109.py, red110.py, red111.py; argument 2: the directory of experiments/044/red_reproduce.py) on
this Design's instance rules, with red's own seeds."""
import sys, importlib.util; sys.path.insert(0, sys.argv[1])
import numpy as np, warnings, collections
from multiprocessing import Pool
import red109 as R, red110 as R110, red111 as R111
warnings.simplefilter('ignore'); GAM = R.GAM
spec = importlib.util.spec_from_file_location('e044', sys.argv[2] + '/red_reproduce.py'); E44 = importlib.util.module_from_spec(spec)
sys.argv = sys.argv[:2]; spec.loader.exec_module(E44)


def draw110(seed):
    rng = np.random.default_rng([4045, seed]); N = [1, 3, 6][seed % 3]
    bA = rng.uniform(0.3, 1.5, N) * np.where(rng.random(N) < 1 / 3, -1, 1); sd = rng.uniform(0.001, 0.01)
    xb = rng.choice([0.25, 1.0], N)
    I = dict(BE=np.array([[1.0]]), BA=bA[:, None], Sf=np.array([[0.08 ** 2 + sd ** 2]]), lam=np.array([rng.uniform(-0.01, 0.03)]), cE=np.array([rng.uniform(0, 0.002)]),
             ah=rng.uniform(-0.01, 0.01, N), V=0.02 ** 2 * (1 + rng.uniform(0.01, 3, N)), kpA=rng.uniform(0, 0.02, N), kmA=rng.uniform(0, 0.02, N),
             kpE=np.array([rng.uniform(0, 0.005)]), kmE=np.array([rng.uniform(0, 0.005)]),
             SE=np.array([[rng.uniform(0.005 ** 2, 0.02 ** 2)]]) if seed % 6 == 5 else np.zeros((1, 1)), xb=xb,
             x0E=np.array([0.0 if rng.random() < 0.5 else rng.uniform(0, 0.5)]), h=10.0)
    I['x0A'] = rng.uniform(0, 1, N) * xb
    r0 = R.solve(I)
    if r0 is None: return None
    x = r0[0]; mu, Sig, kp, km, x0 = R.mom(I); need = np.sum(x - x0) + kp @ np.maximum(x - x0, 0) + km @ np.maximum(x0 - x, 0)
    I['h'] = max(need * rng.uniform(0.3, 1.5), 1e-3)
    return I


def job110(seed):
    I = draw110(seed)
    if I is None: return None
    s = R.solve(I)
    if s is None: return None
    x, eta_s, _, _ = s; N = len(I['ah']); xa, p, m, st, eta = R110.rule(I)
    return dict(err=float(max(np.abs(xa - x[:N]).max(), abs(p - x[N]))), st=st, bind=eta > 0, sE=I['SE'][0, 0] > 0, deta=abs(eta - eta_s))


def job111(seed):
    I = E44.draw(seed)
    if I is None: return None
    N = len(I['ah']); M = 2; Q = I['BA'].T.copy(); SEE = I['Sf']
    J = R111.fibre(I, None); s1 = R111.fibre(I, None, fixA=True)
    if J is None or s1 is None: return None
    xJ, Jv, _, _ = J; x1, _, _, eta1 = s1; w1 = x1[N:] + Q @ I['x0A']; wJ = xJ[N:] + Q @ xJ[:N]
    f = R111.fibre(I, w1)
    if f is None: return dict(fundable=False)
    x2, T, lam, eta2 = f; Lam = Jv - T; d = wJ - w1
    fd = R111.fibre(I, w1 + 1e-4 * d / max(np.linalg.norm(d), 1e-12)) if np.linalg.norm(d) > 1e-9 else None
    s = lam
    if fd is not None:
        slope = (fd[1] - T) / 1e-4; dv = d / np.linalg.norm(d)
        if abs(slope - (-lam) @ dv) < abs(slope - lam @ dv): s = -lam
    Si = np.linalg.inv(SEE); ub = min(s @ d, s @ Si @ s / (2 * GAM)); dA = xJ[:N] - x2[:N]
    lb = GAM / 2 * (dA @ (I['V'] * dA) + d @ SEE @ d); exact = np.abs(x2 - xJ).max() <= 1e-5
    mu, Sig, kp, km, x0 = R.mom(I); g1 = mu - GAM * Sig @ x1; held = True
    for i in range(N):
        lo = -np.inf if I['x0A'][i] <= 0 else eta1 - (1 + eta1) * I['kmA'][i]; hi = np.inf if I['x0A'][i] >= I['xb'][i] else eta1 + (1 + eta1) * I['kpA'][i]
        held &= lo - 1e-9 <= g1[i] <= hi + 1e-9
    k1 = I['h'] - np.sum(x1 - x0) - (kp @ np.maximum(x1 - x0, 0) + km @ np.maximum(x0 - x1, 0))
    k2 = I['h'] - np.sum(x2 - x0) - (kp @ np.maximum(x2 - x0, 0) + km @ np.maximum(x0 - x2, 0))
    slack = (k1 > 1e-9 and eta1 <= 1e-9) and (k2 > 1e-9 and eta2 <= 1e-9)            # the Design's Deviation 2 rule
    dir1 = np.sign(np.round(x1[N:] - I['x0E'], 7)); dir2 = np.sign(np.round(x2[N:] - I['x0E'], 7))
    c3b = bool(np.all(dir1 != 0) and np.all(x1[N:] > 1e-7) and np.all(dir1 == dir2) and np.all(x2[N:] > 1e-7) and slack)
    return dict(fundable=True, lb=lb <= Lam + 1e-9, ub=Lam <= ub + 1e-9, gap=np.sqrt(d @ SEE @ d) <= np.sqrt(s @ Si @ s) / GAM + 1e-9, exact=exact,
                held=held, c3b=c3b, s0_inexact=bool(np.abs(s).max() < 1e-9 and not exact), Lam=Lam)


if __name__ == "__main__":
    # serial: spawned workers would re-run the module-level loading of experiment 044's script
    A = [o for o in map(job110, range(600)) if o]; B = [o for o in map(job111, range(1000)) if o]
    e = np.array([o['err'] for o in A])
    print(f"claim 110: {len(A)} draws (binding {sum(o['bind'] for o in A)}, sigma_E > 0 at {sum(o['sE'] for o in A)}); statuses {dict(collections.Counter(o['st'] for o in A))}; "
          f"max |holdings rule - solver| {e.max():.1e} (median {np.median(e):.1e}); max |eta - dual| {max(o['deta'] for o in A):.1e}")
    F = [o for o in B if o['fundable']]
    print(f"claim 111: {len(B)} draws, fundable {len(F)}; part 1 lower {sum(o['lb'] for o in F)}, upper {sum(o['ub'] for o in F)}, gap {sum(o['gap'] for o in F)} of {len(F)}; zero s at inexact {sum(o['s0_inexact'] for o in F)}")
    print(f"  exact {sum(o['exact'] for o in F)}; 3a held at x1: {sum(o['held'] for o in F)}, exact {sum(o['exact'] for o in F if o['held'])}; 3b: {sum(o['c3b'] for o in F)}, exact {sum(o['exact'] for o in F if o['c3b'])}")
