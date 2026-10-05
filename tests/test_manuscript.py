"""Public API regressions against independently checked, unchanged paper cases."""
import json
from pathlib import Path
import numpy as np
import pytest
from etfport import compare_policies
from etfport.examples import make_example

ROWS=json.loads((Path(__file__).parent/'fixtures.json').read_text())

@pytest.mark.parametrize('scenario',list(ROWS))
def test_manuscript_forecast_case(scenario):
    expected=ROWS[scenario];P=make_example(scenario);actual=compare_policies(P)
    assert P.portfolio.holdings==pytest.approx(expected['initial_x'],abs=1e-6)
    assert actual.planning_gain_bp==pytest.approx(expected['gain_bp'],abs=1e-5)
    assert actual.current_fund_benefit_bp==pytest.approx(expected['current_fund_permission_gain_bp'],abs=1e-5)
    for pub,old in [('etf_only','etf_only'),('one_review','myopic'),('planning','dynamic')]:
        r=getattr(actual,pub)
        assert r.current.holdings==pytest.approx(expected[old]['x'],abs=1e-5)
        assert r.value*1e4==pytest.approx(expected[old]['value_bp'],abs=1e-5)
        assert r.current.transaction_cost*1e4==pytest.approx(expected[old]['cost0_bp'],abs=1e-5)
        assert r.current.holdings.sum()+r.current.cash+r.current.transaction_cost==pytest.approx(P.portfolio.wealth,abs=1e-8)
        for state,action in zip(P.scenarios,r.future):
            available=state.gross_returns@r.current.holdings+r.current.cash
            assert action.holdings.sum()+action.cash+action.transaction_cost==pytest.approx(available,abs=1e-8)
            assert action.cash>=-2e-7
            assert np.min(action.holdings)>=-2e-7
