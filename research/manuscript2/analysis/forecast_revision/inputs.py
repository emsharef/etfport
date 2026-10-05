"""Conditional M9 forecast-revision scenarios; all inputs assumed, DESIGN.md."""
from pathlib import Path
import sys
import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE.parent / 'diversified'))
import menu as D

SCENARIOS = ['unchanged', 'premium_down_persistent', 'premium_up_persistent',
             'premium_down_reverting', 'premium_up_reverting', 'alpha_up', 'alpha_down',
             'anticipated_down', 'anticipated_up']
NAMES = D.NAMES

def beliefs(c, old=False):
    prior = np.r_[D.LAM, D.ALPHA + c.get('alpha_offset_bp', 0) / 1e4]
    current = prior.copy(); long_run = prior.copy()
    name = 'unchanged' if old else c['scenario']
    if name.startswith('premium_') or name.startswith('anticipated_'):
        delta = np.linalg.solve(D.BE, np.array([-.0015, .0005, 0.]))
        if '_up' in name:
            delta = -delta
        if name.startswith('anticipated_'):
            long_run[:3] += delta / .2
        else:
            current[:3] += delta
            if name.endswith('persistent'):
                long_run = current.copy()
    elif name in ('alpha_up', 'alpha_down'):
        current[3] += (.0005 if name == 'alpha_up' else -.0005)
        long_run = current.copy()
    else:
        assert name == 'unchanged'
    return current, long_run

def build(c, old=False, free=False):
    m, tb = beliefs(c, old)
    rates = np.r_[np.full(6, c['fund_bp']), np.full(3, c['etf_bp'])] / 1e4
    if free:
        rates *= 0
    return D.mn_model(BA=D.BA, BE=D.BE, lam=m[:3], alpha=m[3:],
                      premium_sd=D.PL_SD*c['uncertainty'], alpha_sd=D.PA_SD*c['uncertainty'],
                      sigma_f=D.SF, sigma_A=D.SA, sigma_E=D.SE, cE=D.FEE,
                      gamma=c['gamma'], beta=1., kp=rates, km=rates, cap=np.full(9, np.inf),
                      phi=np.full(9, .8), q=D.STATE_SD**2, theta_bar=tb,
                      law='axis', observe_factor=True)

def cases():
    configurations = [(2.5, .5, 0), (2.5, 1., 0), (2.5, 2., 0),
                      (2., 1., 0), (3., 1., 0), (2.5, 1., -5)]
    out = []
    for gamma, uncertainty, offset in configurations:
        for scenario in SCENARIOS:
            out.append(dict(block='core', gamma=gamma, uncertainty=uncertainty,
                            alpha_offset_bp=offset, fund_bp=5., etf_bp=2., scenario=scenario))
    for fund, etf in [(0, 0), (0, 2), (20, 2), (5, 0), (5, 5), (20, 5)]:
        for scenario in SCENARIOS:
            out.append(dict(block='costs', gamma=2.5, uncertainty=1., alpha_offset_bp=0,
                            fund_bp=float(fund), etf_bp=float(etf), scenario=scenario))
    assert len(out) == 108
    return [dict(case_id=i, **c) for i, c in enumerate(out)]

def baseline(c):
    return (c['gamma'], c['uncertainty'], c['alpha_offset_bp'], c['fund_bp'], c['etf_bp']) == (2.5, 1., 0, 5., 2.)
