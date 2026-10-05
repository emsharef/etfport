"""Assemble a focused review/submission bundle; exclude unused legacy figures."""
from pathlib import Path
import csv,json,re,shutil,zipfile
HERE=Path(__file__).resolve().parent
PAPER=HERE.parents[1];BUILD=PAPER/'build'

def main():
    diag=json.loads((HERE/'diagnostics.json').read_text())
    manifest=json.loads((PAPER/'formal_source_manifest.json').read_text())
    guide=['# Formal-verification supplement','',
      'This supplement supplies source locations for the results of *When Forecasts Change: Rebalancing Active Funds and ETFs*. The article states mathematical assumptions and verification limits in Appendix A; the locators below are for reproducing the formal checks.','',
      f"Lean toolchain: `{manifest['lean']}`. Mathlib revision: `{manifest['mathlib_revision']}`.",'',
      '`formal-source.zip` contains the Lean statements, proof modules, explicit hypotheses for cited mathematics and dependency pins. Its `SOURCE_MANIFEST.json` records the repository revision and SHA-256 hashes. `FORMAL_STATEMENTS.txt` gives exact common-multiplier and two-review declarations with a notation guide. The external mathematical hypotheses remain hypotheses; the numerical policies are not machine checked.','',
      'A permanent public archive and DOI have not been deposited. The local bundle is a review artifact, not fulfillment of the outstanding archival condition for publication.','',
      '| Article result | Statement file in `lean/Standalone/` | Declarations / scope |','|---|---|---|',
      '| Proposition 1; Corollary 2 | `M7FundHoldBuySellCriterion.lean` | `SpanningRule`, `Criterion`, `EtfTest` |',
      '| Proposition 3 | `M7OneEtfTwoScalars.lean` | `One`, `OnePrice`, ETF regimes and cash monotonicity |',
      '| Proposition 4 | `M7IncumbentAwareFirstStage.lean` | `FibreMult`, `LossBounds`, `Exactness` |',
      '| Proposition 5 | `M5PartialAdjustmentSplit.lean` | `LQ`, `BellmanVerif`, `Aim`, `Separation` |',
      '| Equation (19), learning bound | `M5LearningAimTwoSpeeds.lean`, `M5WhenAnticipationMatters.lean`, `IntegrationTheorem.lean` | Scalar learning and anticipation bounds; `AnticipationOrder` |',
      '| Equation (20), quadratic gap | `M5PlugInValueLoss.lean` | `OneStep`, `Pathwise`, `Stability`; expected telescoping is a paper proof |',
      '| Proposition 6 | `M7DynamicBundlingBand.lean`, `M7DynamicBundlingShape.lean` | `EffectiveBand`, `ResidualCeiling`, `Frictionless`, `Edges`, `Monotone2` |',
      '| Corollaries 7–8 | `M7TwoReviewsBindingBudget.lean` | `Tomorrow`, `Root`, `MyopicTest`, costless specialization |',
      '| Equations (25)–(26) and interior-trade implications | `M7TwoReviewsBounds.lean` | `CashPriceBound`, `SlackWhenCovered`, `DynamicCashPrice`, `Brackets`, `InteriorTrade`, `InteriorTradeBinding` |',
      '| Unspanned reduction, Appendix B.2 | `M5MissingDirectionLeak.lean` | Hedged-premium and residual-risk identities |',
      '| Finite learning example, Appendix E.1 | `M8WorkedLearningExample.lean` | Filter/current moment identities; numerical policy comparison is not formalized |','',
      'Proof modules are in `lean/Novel/`; external hypotheses are in `lean/Upstream/`. With the pinned dependencies installed, unpack the source archive, enter `lean/`, and run `lake build Audit`. The Mathlib compiled cache is not bundled; restoring dependencies requires network access.','']
    (PAPER/'FORMAL_SOURCE_GUIDE.md').write_text('\n'.join(guide))
    lines=['# Numerical supplement: illustrative forecast revisions','',
      'The inputs are assumed. All benefits below are differences in the additive quarterly mean–variance score, normalized by initial wealth. They are not realized or annualized returns. Transaction costs and the stipulated risk charge are already deducted. No empirical calibration or long-horizon gain is established.','',
      'The current fund-trading benefit compares joint and ETF-only one-review optimization. The planning gain compares the full two-review policy with repeated one-review optimization, evaluated over the same two reviews. Both policies can trade every instrument next quarter.','',
      '| Design | Cases | Median planning gain, bp | Maximum planning gain, bp | Maximum current fund benefit, bp |','|---|---:|---:|---:|---:|']
    for k in ('revisions','extension'):
      r=diag[k];lines.append(f"| {k} | {r['cases']} | {r['median_planning_gain_bp']:.6f} | {r['max_planning_gain_bp']:.6f} | {r['max_current_fund_benefit_bp']:.6f} |")
    lines+=['','These medians summarize the specified grids, which include controls and duplicate no-news configurations; they do not estimate a population median.','',
      '## Complete trades and score comparisons','',
      '`instrument_trades.csv` supplies every instrument’s starting holding, current trade, post-trade holding and expected next-review trade for all 157 cases and all three policies. Holdings and trades are percentages of initial wealth. Cash and current trading cost are also reported; sales finance purchases and costs. `case_metrics.csv` supplies both benefit measures and current/expected next-review transaction costs for each policy. Source and case identifiers match the complete original case data in the bundle.','',
      '## Cash prices for the three Figure 2 cases','',
      'These are solver-selected multipliers from independently constructed quadratic programs. Multipliers measure marginal score per dollar of relaxed funding, not basis points of portfolio return. The effective current price includes expected future cash value. A fixed-policy continuation program does not identify an economically comparable root multiplier, so the repeated one-review root is solved separately.','',
      '| Forecast | One-review root multiplier | Planned root multiplier | Planned mean next multiplier | Effective planned current price | Planned next min | Planned next max |','|---|---:|---:|---:|---:|---:|---:|']
    for r in diag['duals']:
      d=r['dynamic'];lines.append(f"| {r['scenario']} | {r['myopic_root_eta']:.8f} | {d['eta0']:.8f} | {d['eta1_mean']:.8f} | {d['effective_eta0']:.8f} | {d['eta1_min']:.8f} | {d['eta1_max']:.8f} |")
    lines+=['','Cash is zero to numerical tolerance at both reviews. In both policies all next-review multipliers exceed 1e-7; the separately solved one-review root and the joint planned root are also positive. This establishes a positive marginal cash value for the selected solutions, not a decomposition of the planning gain into funding and cost-timing contributions. Multiplier nonuniqueness is possible.','',
      f"Maximum holding discrepancy with the original calculations: {max(r['max_holding_error'] for r in diag['duals']):.3g} of wealth. Maximum value discrepancy: {max(r['max_value_error_bp'] for r in diag['duals']):.3g} bp. Solver warnings: {sum(len(r['warnings']) for r in diag['duals'])}.",'',
      '## Fee credit and the negative-alpha case','',
      'Fee credits are obtained by multiplying the fund loading matrix in ETF units by the ETF fee vector: '+', '.join(f'{x:.2f}' for x in diag['fee_credit_bp'])+' bp per quarter. This is an algebraic expected-payoff comparison at fixed factor exposure, not a fee-ablation estimate of fund allocations.','',
      '| Forecast in all-negative-old-alpha configuration | Gross fund trade, one review (% wealth) | Gross fund trade, planning (% wealth) |','|---|---:|---:|']
    for r in diag['negative_alpha']:
      lines.append(f"| {r['scenario']} | {r['myopic']['fund_gross_trade_pct']:.5f} | {r['dynamic']['fund_gross_trade_pct']:.5f} |")
    lines+=['','Initial fund share is 21.4269%; the remaining capital is in ETFs and starting cash is zero. No claim is made that this assumed configuration represents the average mutual fund.','',
      '## Reproduction','',
      'The analysis design was saved before recovering the omitted budget diagnostics. `analysis/review_round4/analyze.py` exports the two CSVs and solves the three selected dual diagnostics without changing any economic input. Its independent tree construction is `analysis/forecast_revision/verify.py`. The other designs, result files, verification records and source inputs are included under their respective analysis directories. Full source hashes, tolerances, conditional duals and warnings are in `diagnostics.json`.','']
    (PAPER/'NUMERICAL_SUPPLEMENT.md').write_text('\n'.join(lines))
    BUILD.mkdir(exist_ok=True)
    # The formal supplement is self-contained apart from pinned external dependencies.
    with zipfile.ZipFile(BUILD/'formal-verification.zip','w',zipfile.ZIP_DEFLATED) as z:
      for name in ('formal-source.zip','formal_source_manifest.json','FORMAL_STATEMENTS.txt','FORMAL_SOURCE_GUIDE.md'):
        z.write(PAPER/name,name)
    for name in ('NUMERICAL_SUPPLEMENT.md','FORMAL_SOURCE_GUIDE.md'):shutil.copyfile(PAPER/name,BUILD/name)
    for name in ('instrument_trades.csv','case_metrics.csv','diagnostics.json'):shutil.copyfile(HERE/name,BUILD/name)
    image_names=re.findall(r'!\[[^\]]*\]\((figures/[^)]+)\)',(PAPER/'MANUSCRIPT.md').read_text())
    assert len(image_names)==5
    included=[PAPER/'MANUSCRIPT.md',PAPER/'references.bib',PAPER/'NUMERICAL_SUPPLEMENT.md',PAPER/'FORMAL_SOURCE_GUIDE.md',PAPER/'formal-source.zip',PAPER/'formal_source_manifest.json',PAPER/'FORMAL_STATEMENTS.txt',BUILD/'main.pdf',PAPER/'RESPONSE_TO_REVIEWER_ROUND4.md']
    for name in image_names:
      included += [PAPER/name,(PAPER/name).with_suffix('.pdf')]
    for folder in ('forecast_revision','forecast_extension','diversified','review_round4'):
      included += [p for p in (PAPER/'analysis'/folder).iterdir() if p.is_file() and p.suffix in {'.md','.py','.json','.csv'}]
    with zipfile.ZipFile(BUILD/'review-bundle.zip','w',zipfile.ZIP_DEFLATED) as z:
      for p in included:z.write(p,str(p.relative_to(PAPER.parent)))
      # Local model/solver dependencies preserve reproducibility without modifying them.
      for rel in ('experiments/d16-harness/harness_n.py','experiments/d26-prep/policies.py','uv.lock','pyproject.toml'):
        z.write(PAPER.parent/rel,rel)
    print('Prepared focused review bundle with only the five figures used in the article.')
if __name__=='__main__':main()
