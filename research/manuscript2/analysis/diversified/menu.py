"""Prespecified diversified M9 menu. All numbers are assumed; see DESIGN.md."""
from pathlib import Path
import sys
import numpy as np
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/"experiments/d16-harness"))
from harness_n import mn_model

NAMES=["Equity A","Equity B","Duration A","Duration B","Credit A","Credit B",
       "Equity ETF","Duration ETF","Credit ETF"]
BE=np.array([[1,0,0],[0,1,0],[.2,4/15,1.]])
Q=np.array([[1.05,0,0],[.9,.05,.1],[0,1.1,0],[.05,.9,.05],[.05,0,1.],[0,.15,.9]])
BA=Q@BE
LAM=np.array([.012,.003,.0028])
SF=np.array([.08,.03,np.sqrt(.00128)])
PL_SD=np.array([.004,.0015,.002])
ALPHA=np.array([4,2,1,.5,3,1])/1e4
SA=np.array([.04,.05,.015,.02,.025,.03])
PA_SD=np.array([20,30,10,15,15,25])/1e4
SE=np.array([.001,.0005,.001])
FEE=np.array([2,1,3])/1e4
STATE_SD=np.array([.001,.0005,.0008]+[.0005]*6)
STARTS={"cash":(np.zeros(9),1.),
        "etfs":(np.r_[np.zeros(6),np.ones(3)/3],0.),
        "funds":(np.r_[np.ones(6)/6,np.zeros(3)],0.),
        "mixed":(np.array([.1,.05,.05,.05,.1,.05,.25,.1,.2]),.05)}

def build(gamma=2.5,uncertainty=1.,alpha_scale=1.,fund_bp=5.,etf_bp=2.,forecast="steady",**_):
    am=ALPHA*alpha_scale;tb=np.r_[LAM,am];move=np.zeros(9)
    if forecast=="manager_rotation":move[3:]=am[[1,0,3,2,5,4]]-am
    elif forecast in ("premium_rotation","premium_reverse"):
        sleeve=np.array([-.0015,.0005,0.])*(1 if forecast=="premium_rotation" else -1)
        move[:3]=np.linalg.solve(BE,sleeve)
    else:assert forecast=="steady"
    tb=tb+move/.2
    rates=np.r_[np.full(6,fund_bp),np.full(3,etf_bp)]/1e4
    return mn_model(BA=BA,BE=BE,lam=LAM,alpha=am,premium_sd=PL_SD,sigma_f=SF,sigma_A=SA,
                    alpha_sd=PA_SD*uncertainty,sigma_E=SE,cE=FEE,gamma=gamma,beta=1.,
                    kp=rates,km=rates,cap=np.full(9,np.inf),phi=np.full(9,.8),q=STATE_SD**2,
                    theta_bar=tb,law="axis",observe_factor=True)

def sleeves(x):return Q.T@np.asarray(x)[:6]+np.asarray(x)[6:]
