"""Explicit JSON inputs: all numerical forecasts and costs are supplied by the user."""
import json
from pathlib import Path
import numpy as np
from .models import AllocationProblem, Moments, Portfolio, Scenario, TradingCosts


def load_problem(path):
    data=json.loads(Path(path).read_text())
    def moments(d):return Moments(d['mean'],d['covariance'])
    states=tuple(Scenario(s['probability'],s['gross_returns'],moments(s),s.get('label','')) for s in data.get('scenarios',[]))
    return AllocationProblem(moments(data),Portfolio(data['holdings'],data['cash']),
      TradingCosts(data['buy_costs'],data['sell_costs']),data['gamma'],tuple(data.get('names',[])),
      tuple(data.get('fund_indices',[])),
      None if 'caps' not in data else np.array([np.inf if v is None else v for v in data['caps']]),
      states,data.get('discount',1.))
