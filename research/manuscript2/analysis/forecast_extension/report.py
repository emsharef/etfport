"""Report the extended scenarios and generate the manuscript's decision figures."""
import hashlib
import json
import os
os.environ.setdefault('MPLCONFIGDIR','/tmp/proof-etfport-mpl')
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import extension_inputs as S

FIG=S.HERE.parents[1]/'figures'

def clean(v,n=4):
    return f'{0 if abs(v)<.5*10**(-n) else v:.{n}f}'

def figures(rows):
    previous=json.loads((S.HERE.parent/'forecast_revision/results.json').read_text())['results']
    base={r['scenario']:r for r in previous if (r['gamma'],r['uncertainty'],r['alpha_offset_bp'],r['fund_bp'],r['etf_bp'])==(2.5,1,0,5,2)}
    scenarios=['premium_down_persistent','alpha_up','alpha_down']
    titles=['Equity premium 120 → 105 bp\nDuration premium 30 → 35 bp',
            'Equity A alpha 4 → 9 bp','Equity A alpha 4 → -1 bp']
    fig,axes=plt.subplots(1,3,figsize=(10.8,4.8))
    for ax,key,title in zip(axes,scenarios,titles):
        r=base[key]
        ids=[i for i in range(9) if max(abs(r[p]['trade'][i]) for p in ('myopic','dynamic'))>.0001]
        yy=np.arange(len(ids))
        for p,offset,color,label in [('myopic',-.18,'#427AA1','One-quarter'),('dynamic',.18,'#C65D21','Plan ahead')]:
            vals=np.array(r[p]['trade'])[ids]*100
            ax.barh(yy+offset,vals,height=.3,color=color,label=label)
            for y,v in zip(yy+offset,vals):
                ax.text(v+(.18 if v>=0 else -.18),y,'0' if abs(v)<.005 else f'{v:+.1f}',
                        va='center',ha='left' if v>=0 else 'right',fontsize=12,color=color)
        ax.set_yticks(yy,[S.NAMES[i] for i in ids]);ax.invert_yaxis()
        ax.set_xlim(-11.5,11.5);ax.set_xticks([-10,-5,0,5,10]);ax.axvline(0,color='#555',lw=.8)
        ax.set_title(title,fontsize=12,pad=12)
        ax.set_xlabel('Sale ←   % of wealth   → Purchase',fontsize=11)
        ax.tick_params(labelsize=11)
        ax.text(.5,-.34,f"Net planning gain: {r['gain_bp']:.3f} score bp",transform=ax.transAxes,ha='center',fontsize=10)
        ax.spines[['top','right']].set_visible(False);ax.grid(axis='x',alpha=.15);ax.set_axisbelow(True)
    hh,ll=axes[0].get_legend_handles_labels()
    fig.legend(hh,ll,ncol=2,loc='upper center',bbox_to_anchor=(.5,.94),frameon=False,fontsize=12)
    fig.suptitle('Trades after new forecasts, from the old optimal portfolio',fontsize=14,y=1.01)
    fig.subplots_adjust(left=.09,right=.99,top=.73,bottom=.24,wspace=.58)
    for ext in ('png','pdf'):fig.savefig(FIG/f'fig2_forecast_revision.{ext}',dpi=180,bbox_inches='tight')
    plt.close(fig)

    select=lambda p:sorted([r for r in rows if r['menu']=='unspanned' and r['style_prior_bp']==20 and r['persistence']==p],key=lambda r:r['revision_bp'])
    persistent=select('persistent');reverting=select('reverting')
    xx=[r['revision_bp'] for r in persistent]
    fig,axes=plt.subplots(1,2,figsize=(10.5,4.8),sharey=True)
    for p,color,marker,label in [('etf_only','#777777','s','ETF-only'),('myopic','#427AA1','o','Joint one-quarter'),('dynamic','#C65D21','D','Plan ahead')]:
        axes[0].plot(xx,[r[p]['factor_exposures'][3] for r in persistent],marker=marker,color=color,label=label,lw=1.7,ms=5)
    axes[1].plot(xx,[r['myopic']['factor_exposures'][3] for r in persistent],'o:',color='#427AA1',label='Joint one-quarter',lw=1.5,ms=4)
    axes[1].plot(xx,[r['dynamic']['factor_exposures'][3] for r in persistent],'D-',color='#C65D21',label='Plan: persistent',lw=1.7,ms=5)
    axes[1].plot(xx,[r['dynamic']['factor_exposures'][3] for r in reverting],'^--',color='#23856D',label='Plan: 80% remains next quarter',lw=1.7,ms=5)
    for ax,title in zip(axes,['A. ETFs cannot change this exposure','B. Persistence changes today’s response']):
        ax.set_title(title,fontsize=12,pad=12);ax.set_xlabel('Revised style premium (bp per quarter)',fontsize=12)
        ax.axvline(0,color='#999',lw=.6);ax.axhline(0,color='#999',lw=.6)
        ax.set_xticks(xx);ax.set_ylim(-.38,.47);ax.grid(alpha=.15);ax.spines[['top','right']].set_visible(False)
        ax.legend(loc='upper left',frameon=False,fontsize=9.5)
        ax.tick_params(labelsize=11)
    axes[0].set_ylabel('Style exposure\nper dollar of initial wealth',fontsize=12)
    fig.suptitle('Same alpha estimates; a revised premium outside the ETF span',fontsize=14,y=.99)
    fig.subplots_adjust(left=.08,right=.98,top=.79,bottom=.19,wspace=.16)
    for ext in ('png','pdf'):fig.savefig(FIG/f'fig3_unspanned_forecast.{ext}',dpi=180,bbox_inches='tight')
    plt.close(fig)
    paths=[S.HERE/'results.json',S.HERE.parent/'forecast_revision/results.json',S.HERE/'report.py']
    manifest=dict(figure2=dict(scenarios=scenarios,source='analysis/forecast_revision/results.json',measure='current trades, percent of initial wealth'),
                  figure3=dict(style_prior_bp=20,revisions_bp=xx,source='analysis/forecast_extension/results.json',measure='style factor exposure per dollar of initial wealth'),
                  source_hashes={str(p.relative_to(S.ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths})
    (FIG/'forecast_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')

def main():
    rows=json.loads((S.HERE/'results.json').read_text())['results']
    verify=json.loads((S.HERE/'verification_comparison.json').read_text())
    vraw=json.loads((S.HERE/'verification.json').read_text())
    styles=[r for r in rows if r['menu']=='unspanned']
    invariance=[]
    for sd in (10,20,40):
        rr=[r for r in styles if r['style_prior_bp']==sd]
        ctrl=next(r for r in rr if r['revision_bp']==0)
        err=max(np.max(abs(np.array(r['etf_only']['x'])-ctrl['etf_only']['x'])) for r in rr)
        assert err<1e-6,err
        invariance.append(dict(style_prior_bp=sd,max_etf_only_holding_change=float(err)))
    summary=dict(cases=len(rows),median_planning_gain_bp=float(np.median([r['gain_bp'] for r in rows])),
                 max_planning_gain_bp=max(r['gain_bp'] for r in rows),
                 max_current_fund_permission_gain_bp=max(r['current_fund_permission_gain_bp'] for r in rows),
                 max_objective_error=max(abs(r['objective_error']) for r in rows),
                 min_cash=min(r[p]['future_min_cash'] for r in rows for p in ('myopic','dynamic','etf_only')),
                 joint_retry_cases=[r['case_id'] for r in rows if len(r['joint_attempts'])>1],
                 solver_accuracy_warnings=sum('inaccurate' in w for r in rows for w in r['warnings']),
                 compilation_warnings=sum('subexpressions' in w for r in rows for w in r['warnings']),
                 independent_cases=len(verify),independent_warnings=sum(len(v['warnings']) for v in vraw),
                 max_independent_holding_error=max(v['holding_error'] for v in verify),
                 max_independent_value_error_bp=max(v['value_error_bp'] for v in verify),
                 max_independent_gain_error_bp=max(v['gain_error_bp'] for v in verify),etf_only_invariance=invariance)
    (S.HERE/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    figures(rows)
    out=['# Forecast direction, persistence and missing ETF span','',
         'All inputs are assumed. This extends the controlled old-optimal-incumbent comparison under existing M9; no new theorem or formal source was added. The findings concern the selected conditional forecast scenarios, not empirical performance.','',
         '## Economic distinctions','',
         '- The original menu spans equity, duration and credit, but a zero ETF holding prevents a sale in that instrument. In the credit-premium cut, the best ETF-only action is no trade while the joint policy sells credit funds.',
         '- Adding an economic style factor with zero ETF loadings creates an algebraically missing direction. Alpha remains defined after all four factors. A style-premium revision changes fund selection without an alpha revision.',
         '- At the baseline style prior SD, +/-10 bp style revisions produce no current one-quarter trade but opposite fund switches under planning. Total ETF holdings remain essentially unchanged in both cases.',
         '- Persistent and partly reverting revisions have identical current means and uncertainty, hence the same one-quarter decisions. Their planning decisions differ.',
         '- Each menu and uncertainty specification gets its own old optimal portfolio. All old one-quarter controls make no material trade. No historical trading path or long-run attractor is asserted.','',
         '![Style exposure responses.](../../figures/fig3_unspanned_forecast.png)','',
         '## Full baseline style grid','',
         'Style exposure is a factor sensitivity per dollar of initial wealth, not an allocation weight. Negative values can arise from nonnegative holdings in funds with negative style loadings. The old style exposure is about 0.0842; all old alphas are unchanged throughout the grid.','',
         '| Revision, bp | Forecast | ETF-only exposure | One-quarter exposure | Planning exposure | One-quarter ETF % | Planning ETF % | Planning gain, bp |',
         '|---:|---|---:|---:|---:|---:|---:|---:|']
    for r in styles:
        if r['style_prior_bp']!=20:continue
        out.append(f"| {r['revision_bp']} | {r['persistence']} | {clean(r['etf_only']['factor_exposures'][3])} | {clean(r['myopic']['factor_exposures'][3])} | {clean(r['dynamic']['factor_exposures'][3])} | {clean(r['myopic']['etfs_pct'],2)} | {clean(r['dynamic']['etfs_pct'],2)} | {clean(r['gain_bp'],5)} |")
    out+=['','## Other revised forecasts','','| Scenario | Revision, bp | One-quarter ETF % | Planning ETF % | Current fund-trading benefit, bp | Planning gain, bp |','|---|---:|---:|---:|---:|---:|']
    for r in rows:
        if r['menu']!='spanned':continue
        out.append(f"| {r['scenario']} | {r['revision_bp']} | {clean(r['myopic']['etfs_pct'],2)} | {clean(r['dynamic']['etfs_pct'],2)} | {clean(r['current_fund_permission_gain_bp'],5)} | {clean(r['gain_bp'],5)} |")
    out+=['','## Scope and checks','',
          f"The complete 49-case grid has median planning gain {summary['median_planning_gain_bp']:.5f} bp and maximum {summary['max_planning_gain_bp']:.5f} bp. Those figures describe assumed inputs, not a test of whether the research direction is useful. The largest current one-quarter score benefit from allowing fund trades is {summary['max_current_fund_permission_gain_bp']:.5f} bp; this is a different comparison from planning.",'',
          'The ETF-only invariance check passes at all three prior SDs. Its economic reason is exact: with funds fixed and every ETF loading zero, the style premium multiplies the same inherited style exposure in every current feasible ETF action. No change to a fund alpha estimate is involved. The check says nothing about a policy that can trade funds at the current review, or a different future objective.','',
          f"All joint final solves returned optimal. One case (ID 28) required two retries with the documented stopping settings. The original run records {summary['solver_accuracy_warnings']} accuracy warnings and {summary['compilation_warnings']} CVXPY compilation-size warnings; none is silently dropped. Every root and future budget passed the registered checks. Maximum objective reconstruction error is {summary['max_objective_error']:.3g}; minimum future cash is {summary['min_cash']:.3g}, within solver tolerance.",'',
          f"Independent direct-tree/vectorized-QP checks cover {summary['independent_cases']} cases. Maximum holding error is {summary['max_independent_holding_error']:.3g}, value error {summary['max_independent_value_error_bp']:.3g} bp and planning-gain error {summary['max_independent_gain_error_bp']:.3g} bp. Independent warnings: {summary['independent_warnings']}. This is numerical reproduction, not machine-checked formalization or a change in lab evidence status.",'',
          'The additional factor is independent of the original factors by assumption. A correlated missing direction would require separating the part hedgeable through ETFs; Appendix B.2 gives that reduction under its unconstrained quadratic assumptions. The funded illustrations here do not claim that its closed-form policy transfers.','',
          'The seven plotted points are solved scenarios; connecting lines do not locate exact thresholds. Larger gains were not a design objective. Complete holdings, costs, factor exposures and all 49 cases remain in [results.json](results.json) and [results.csv](results.csv). See [DESIGN.md](DESIGN.md) for inputs and numerical deviations, and [verification_comparison.json](verification_comparison.json) for independent errors.','',
          '```bash','.venv/bin/python manuscript2/analysis/forecast_extension/run.py','.venv/bin/python manuscript2/analysis/forecast_extension/verify.py','.venv/bin/python manuscript2/analysis/forecast_extension/report.py','```','']
    (S.HERE/'REPORT.md').write_text('\n'.join(out))
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
