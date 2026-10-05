"""Report every prespecified case and draw trades from the old optimal portfolio."""
import json
import os
os.environ.setdefault('MPLCONFIGDIR', '/tmp/proof-etfport-mpl')
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import inputs as S

LABELS = {
    'unchanged':'Unchanged forecasts',
    'premium_down_persistent':'Equity premium -15 bp; duration +5 bp, persistent',
    'premium_up_persistent':'Equity premium +15 bp; duration -5 bp, persistent',
    'premium_down_reverting':'Equity premium -15 bp; duration +5 bp, reverting',
    'premium_up_reverting':'Equity premium +15 bp; duration -5 bp, reverting',
    'alpha_up':'Equity A alpha +5 bp, persistent',
    'alpha_down':'Equity A alpha -5 bp, persistent',
    'anticipated_down':'Same current means; next equity -15 bp, duration +5 bp',
    'anticipated_up':'Same current means; next equity +15 bp, duration -5 bp',
}

def fmt(x, digits=3):
    if abs(x) < .5*10**(-digits): x=0
    return f'{x:.{digits}f}'

def main():
    results=json.loads((S.HERE/'results.json').read_text())['results']
    checks=json.loads((S.HERE/'verification_comparison.json').read_text())
    verified=json.loads((S.HERE/'verification.json').read_text())
    extra=json.loads((S.HERE/'sensitivity_verification.json').read_text())
    base={r['scenario']:r for r in results if S.baseline(r)}
    unchanged=base['unchanged']; headline=base['premium_down_persistent']
    initial=np.array(headline['initial_x'])
    keys=('gamma','uncertainty','alpha_offset_bp','fund_bp','etf_bp')
    controls={tuple(r[k] for k in keys):r for r in results if r['scenario']=='unchanged'}
    for r in results:
        control=controls[tuple(r[k] for k in keys)]
        r['gain_minus_control_bp']=r['gain_bp']-control['gain_bp']
    def stats(rows):
        gains=np.array([r['gain_bp'] for r in rows])
        return dict(cases=len(rows),median_gain_bp=float(np.median(gains)),max_gain_bp=float(max(gains)),
                    min_gain_bp=float(min(gains)),above_1bp=int(sum(gains>1)),
                    max_control_adjusted_gain_bp=float(max(r['gain_minus_control_bp'] for r in rows)))
    summary={b:stats([r for r in results if b=='all' or r['block']==b]) for b in ('core','costs','all')}
    summary['max_old_static_error']=max(r['static_error'] for r in results)
    summary['max_old_beliefs_trade']=max(r['old_beliefs_max_trade'] for r in results)
    summary['max_objective_error']=max(abs(r['objective_error']) for r in results)
    summary['min_cash']=min(r[p]['future_min_cash'] for r in results for p in ('myopic','dynamic','etf_only'))
    summary['warning_count']=sum(len(r['warnings']) for r in results)
    summary['independent_warning_count']=sum(len(v['warnings']) for v in verified)
    summary['max_independent_gain_error_bp']=max(v['gain_error_bp'] for v in checks)
    summary['max_independent_holding_error']=max(v['max_holding_error'] for v in checks)
    summary['additional_checks']=len(extra)
    summary['additional_check_warnings']=sum(len(v['warnings']) for v in extra)
    summary['max_additional_gain_error_bp']=max(v['gain_error_bp'] for v in extra)
    summary['max_additional_value_error_bp']=max(v['max_value_error_bp'] for v in extra)
    worst=max(results,key=lambda r:r['gain_bp'])
    summary['max_case']={k:worst[k] for k in ('scenario',)+keys}
    summary['unchanged_controls']=[{k:r[k] for k in keys+('gain_bp',)} for r in controls.values()]
    (S.HERE/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')

    # Each panel shows the actual purchases/sales, rather than unexplained aggregate ETF shares.
    scenarios=['premium_down_persistent','alpha_up','alpha_down']
    short=['Equity premium 120 → 105 bp\nDuration premium 30 → 35 bp',
           'Equity A alpha 4 → 9 bp','Equity A alpha 4 → -1 bp']
    fig,axes=plt.subplots(1,3,figsize=(12.8,5.3))
    colors={'myopic':'#427AA1','dynamic':'#C65D21'}
    for ax,name,title in zip(axes,scenarios,short):
        r=base[name]
        selected=[i for i in range(9) if max(abs(r[p]['trade'][i]) for p in colors)>.0001]
        yy=np.arange(len(selected))
        for p,shift,label in [('myopic',-.18,'One-quarter'),('dynamic',.18,'Plan ahead')]:
            vv=np.array(r[p]['trade'])[selected]*100
            ax.barh(yy+shift,vv,height=.31,color=colors[p],label=label)
            for y,v in zip(yy+shift,vv):
                if abs(v)<.005:
                    ax.text(.18,y,'0',va='center',ha='left',fontsize=10,color=colors[p])
                else:
                    ax.text(v+(.16 if v>0 else -.16),y,f'{v:+.2f}',va='center',
                            ha='left' if v>0 else 'right',fontsize=10,color=colors[p])
        ax.set_yticks(yy,[S.NAMES[i] for i in selected]);ax.invert_yaxis()
        ax.axvline(0,color='#555555',lw=.7)
        ax.set_xlim(-11,11);ax.set_xticks([-10,-5,0,5,10])
        ax.set_xlabel('Sell ←   % of initial wealth   → Buy',fontsize=10)
        ax.set_title(title,fontsize=11,pad=16)
        ax.text(.5,-.25,f"Planning gain: {r['gain_bp']:.3f} bp",transform=ax.transAxes,ha='center',fontsize=10)
        ax.spines[['top','right']].set_visible(False)
        ax.grid(axis='x',alpha=.13);ax.set_axisbelow(True)
    handles,labels=axes[0].get_legend_handles_labels()
    fig.legend(handles,labels,loc='upper center',bbox_to_anchor=(.5,.915),ncol=2,frameon=False,fontsize=10)
    fig.suptitle('New forecasts, starting from the old optimal portfolio',fontsize=15,y=.98)
    fig.text(.5,.045,'Unchanged forecasts: neither policy trades today. All inputs assumed; both policies remain fully funded.',
             ha='center',fontsize=10)
    fig.subplots_adjust(left=.09,right=.99,bottom=.27,top=.76,wspace=.56)
    for ext in ('png','pdf'):
        fig.savefig(S.HERE/f'forecast_revision_trades.{ext}',dpi=180,bbox_inches='tight')
    plt.close(fig)

    lines=['# Responding to new forecasts from an already optimal portfolio','',
           'All inputs are assumed. This is a conditional numerical application of existing M9, not a backtest or a new theorem. The starting portfolio uses only old beliefs. Both policies respect the funded budget at both reviews.','',
           '## What the control establishes','',
           f"Under unchanged beliefs, the baseline one-quarter and two-review policies both leave the starting holdings unchanged (planning gain {fmt(unchanged['gain_bp'],6)} bp). Thus the forecast-response examples below do not obtain their gain by correcting an arbitrary initial allocation. This is a result for these cases, not a general no-trade theorem.",'',
           'The inherited portfolio is the old one-quarter optimum without investor trading costs, with acquisition costs treated as sunk. It is an assumed already-held target, not a claim that a previous cost-aware trading path or infinite-horizon policy would land exactly there. We independently reproduce it and verify that actual trading costs leave it optimal for the unchanged one-quarter problem. Future return marking and filtering remain active.','',
           '| Instrument | Old optimal holding | One-quarter after premium revision | Plan ahead after premium revision |',
           '|---|---:|---:|---:|']
    for i,name in enumerate(S.NAMES):
        lines.append(f"| {name} | {fmt(100*initial[i],2)}% | {fmt(100*headline['myopic']['x'][i],2)}% | {fmt(100*headline['dynamic']['x'][i],2)}% |")
    lines += ['',
              'The prespecified headline revision lowers the equity sleeve premium from 120 to 105 bp per quarter and raises duration from 30 to 35 bp; credit stays at 60 bp. The revised means are expected to persist, with uncertain future realizations and further filtering. Current belief variances are held fixed across the revision.','',
              'Both policies sell the equity ETF to buy Duration A. Planning makes a larger adjustment. The ETF-only one-quarter alternative sells the equity ETF and buys the duration ETF instead; it respects the same budget and freezes fund dollar holdings today only.','',
              f"Allowing fund trades improves the current one-quarter score over its ETF-only optimum by {headline['current_fund_permission_gain_bp']:.4f} bp. Separately, planning improves the two-review score over repeated one-quarter optimization by {headline['gain_bp']:.4f} bp. These are distinct comparisons, with different objectives and baselines.",'',
              '![Actual trades after forecast revisions.](forecast_revision_trades.png)','',
              '## All nine baseline scenarios','',
              'The old ETF allocation is 20.47% of initial wealth. All percentages below use initial wealth, so holdings plus cash plus current costs sum to 100%. A small difference between purchase and sale amounts pays trading costs.','',
              '| Forecast scenario | One-quarter ETF | Plan-ahead ETF | One-quarter gross fund trades | Plan-ahead gross fund trades | Planning gain |',
              '|---|---:|---:|---:|---:|---:|']
    for name in S.SCENARIOS:
        r=base[name];m=r['myopic'];d=r['dynamic']
        lines.append(f"| {LABELS[name]} | {fmt(m['etfs_pct'],2)}% | {fmt(d['etfs_pct'],2)}% | {fmt(m['gross_fund_trade_pct'],2)}% | {fmt(d['gross_fund_trade_pct'],2)}% | {fmt(r['gain_bp'],4)} bp |")
    lines += ['',
              'Gross fund trades sum the absolute fund purchases and sales; they are not net fund allocation changes. The reverting forecasts retain the same current revision as their persistent counterparts but expect 20% of it to reverse by the next review. Their one-quarter actions therefore agree; their planning decisions can differ.','',
              'The manager revisions give a particularly direct distinction: the one-quarter policy makes no current trade after either +5 or -5 bp in Equity A alpha, while planning buys after the increase and sells after the decrease. The revised estimate is still uncertain. This illustrates a forecast-dependent trade boundary; it does not imply that every update warrants trading.','',
              'Anticipated premium changes leave current means unchanged. At baseline neither policy trades today, even with planning: knowing about a future change does not automatically justify bringing the trade forward.','',
              '## Current versus future contribution to the planning gain','',
              '| Forecast | Change in current score | Change in expected continuation | Total planning gain |',
              '|---|---:|---:|---:|']
    for name in ('premium_down_persistent','alpha_up','alpha_down'):
        r=base[name];m=r['myopic'];d=r['dynamic']
        lines.append(f"| {LABELS[name]} | {fmt(d['score0_bp']-m['score0_bp'],4)} bp | {fmt(d['continuation_bp']-m['continuation_bp'],4)} bp | {fmt(r['gain_bp'],4)} bp |")
    lines += ['',
              'Current and continuation scores each include their own trading costs and risk charge. The decomposition is an accounting identity. It does not attribute the gain uniquely to learning, funding, or transaction-cost timing. In particular, the ETF change is not by itself a measurement of a liquidity reserve.','',
              '## Sensitivities, including unchanged-beliefs controls','',
              'The complete prespecified grid contains 108 cases, including both directions of forecast revisions, risk aversion 2–3, prior mean-error SD scales 0.5–2 for both premia and alpha, an all-negative-old-alpha configuration, and zero/equal/unequal investor trading costs. State-noise variance and realized-return risk are held separately fixed.','',
              '| Block | Cases | Median gain | Maximum gain | Cases above 1 bp |',
              '|---|---:|---:|---:|---:|']
    for block in ('core','costs','all'):
        s=summary[block]
        lines.append(f"| {block} | {s['cases']} | {fmt(s['median_gain_bp'],4)} bp | {fmt(s['max_gain_bp'],4)} bp | {s['above_1bp']} |")
    lines += ['',f"Largest gain: {worst['gain_bp']:.6f} bp, `{worst['scenario']}`, gamma {worst['gamma']}, prior-SD scale {worst['uncertainty']}, old-alpha offset {worst['alpha_offset_bp']} bp, fund cost {worst['fund_bp']} bp and ETF cost {worst['etf_bp']} bp. It is an extremum, not the selected headline.",'',
              '| Configuration | Unchanged-beliefs planning gain |',
              '|---|---:|']
    for r in controls.values():
        desc=f"gamma {r['gamma']}, SD scale {r['uncertainty']}, alpha offset {r['alpha_offset_bp']} bp, fund/ETF cost {r['fund_bp']}/{r['etf_bp']} bp"
        lines.append(f"| {desc} | {fmt(r['gain_bp'],6)} bp |")
    lines += ['',
              'The control need not vanish in every configuration: tomorrow’s marking, filtering and predictive risk can affect today’s funded allocation even without an expected mean change. `control_comparison.csv` reports each gain minus its matched unchanged-beliefs control; that difference is descriptive, not an additive causal decomposition or proof about flexibility.','',
              '## Interpretation and limits','',
              'The useful framing is a manager responding to revised beliefs while carrying an existing portfolio. Three decisions are visible: whether to trade now, how far to move, and whether to implement through ETFs or active funds. Planning does not systematically demand more or fewer ETFs. The resulting portfolio changes can be visible while the incremental score benefit remains small. These runs do not establish economically large performance gains.','',
              'The previous arbitrary-start examples remain saved. They answer portfolio construction or correction questions; they should not be used to claim that the same gains arise when rebalancing an already optimal portfolio. This new control addresses that confound without changing the opportunity set to manufacture a larger effect.','',
              'All numbers remain illustrative assumptions. The study conditions on forecast revisions; it does not model the news that generated them, simulate a historical path into the incumbent, estimate true alpha, or test out-of-sample returns. Its two-review additive mean-variance objective is not a terminal-wealth utility objective. The finite-law filter is linear rather than an exact posterior. No new theorem or Lean source was introduced.','',
              '## Numerical checks and reproduction','',
              f"All {len(results)} joint solves returned optimal. Maximum independent old-portfolio holding error: {summary['max_old_static_error']:.3g}; maximum one-quarter trade under old beliefs: {summary['max_old_beliefs_trade']:.3g} of initial wealth. Maximum reconstructed objective error: {summary['max_objective_error']:.3g}; minimum future cash: {summary['min_cash']:.3g} (solver-scale tolerance). Recorded main-run warnings: {summary['warning_count']}; independent warnings: {summary['independent_warning_count']}.",'',
              f"A separate implementation reconstructs the baseline state law, moments, linear filter and vectorized QPs, without using the lab's tree or policy solver. Across all nine baseline scenarios it reproduces gains within {summary['max_independent_gain_error_bp']:.3g} bp and holdings within {summary['max_independent_holding_error']:.3g} of initial wealth. This is a numerical check, not machine-checked formalization or a lab evidence-status promotion.",'',
              f"The 90 internal solver warnings were confined to five cost-sensitivity cases (IDs 78, 99, 101, 103, 107). A further independent vectorized-QP calculation checks all five and the largest-gain case (ID 74). All six checks completed with {summary['additional_check_warnings']} warnings, matching gains within {summary['max_additional_gain_error_bp']:.3g} bp and every compared policy value within {summary['max_additional_value_error_bp']:.3g} bp. The original warnings remain recorded; results are in [sensitivity_verification.json](sensitivity_verification.json).",'',
              'The first run stopped at an independent SLSQP line-search failure. Its partial results are preserved in `initial_attempt.jsonl`; the numerical stopping-tolerance change is documented under Deviations in DESIGN.md. No economic scenario changed.','',
              '```bash',
              '.venv/bin/python manuscript2/analysis/forecast_revision/run.py',
              '.venv/bin/python manuscript2/analysis/forecast_revision/verify.py',
              '.venv/bin/python manuscript2/analysis/forecast_revision/report.py',
              '```','',
              'Inputs and source hashes: [results.json](results.json). Full tabular results: [results.csv](results.csv). Design: [DESIGN.md](DESIGN.md). Independent checks: [verification_comparison.json](verification_comparison.json).','']
    (S.HERE/'REPORT.md').write_text('\n'.join(lines))
    import csv
    with (S.HERE/'control_comparison.csv').open('w',newline='') as f:
        fields=['case_id','scenario',*keys,'gain_bp','gain_minus_control_bp']
        w=csv.DictWriter(f,fieldnames=fields);w.writeheader()
        w.writerows({k:r[k] for k in fields} for r in results)
    print(json.dumps(summary,indent=2))

if __name__=='__main__': main()
