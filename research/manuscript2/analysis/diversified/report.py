"""Report static construction and incremental planning separately; plot actual holdings."""
import json,os
import numpy as np
import menu as S
os.environ.setdefault("MPLCONFIGDIR","/tmp/proof-etfport-mpl")
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

R=json.loads((S.HERE/"results.json").read_text())["results"]
T=json.loads((S.HERE/"static_results.json").read_text())
V=json.loads((S.HERE/"verification.json").read_text())
assert len(R)==144
def select(**kw):return [r for r in R if all(r[k]==v for k,v in kw.items())]
def base(start,forecast="steady"):
    return select(gamma=2.5,uncertainty=1.,fund_bp=5.,etf_bp=2.,start=start,forecast=forecast)[0]
checks=[]
for v in V:
    r=base(v["start"],v["forecast"])
    e=abs(r["gain_bp"]-v["gain_bp"])
    h=max(float(np.max(abs(np.array(r[p]["x"])-v[p+"_x"]))) for p in ("myopic","dynamic"))
    assert e<1e-4 and h<1e-4,(v["start"],v["forecast"],e,h)
    checks.append(dict(start=v["start"],forecast=v["forecast"],gain_difference_bp=e,max_holding_difference=h))
(S.HERE/"verification_comparison.json").write_text(json.dumps(checks,indent=2)+"\n")
def stats(rows):
    g=np.maximum([r["gain_bp"] for r in rows],0)
    return dict(n=len(rows),median=float(np.median(g)),maximum=float(max(g)),minimum=float(min(g)),
                above_1=int(sum(g>1)),max_weight=float(max(r[p]["max_weight"] for r in rows for p in ("myopic","dynamic"))),
                minimum_positions=min(r[p]["positions_above_1pct"] for r in rows for p in ("myopic","dynamic")))
summary=dict(all=stats(R),core=stats(select(block="core")),costs=stats(select(block="costs")),
             warnings=sum(len(r["warnings"]) for r in R),max_objective_error=max(abs(r["objective_error"]) for r in R),
             min_cash=min(min(r[p]["cash"],r[p]["future_min_cash"]) for r in R for p in ("myopic","dynamic")),
             maximum_case=max(R,key=lambda r:r["gain_bp"]))
(S.HERE/"summary.json").write_text(json.dumps(summary,indent=2)+"\n")

# A direct holdings comparison, with no performance-maximizing case selection.
r=base("cash")
plt.rcParams.update({"font.family":"DejaVu Sans","font.size":10,"pdf.fonttype":42})
fig,ax=plt.subplots(figsize=(9.3,5.5))
y=np.arange(9)
for policy,shift,color,label in (("myopic",-.18,"#557A95","One quarter"),("dynamic",.18,"#D18A34","Plan ahead")):
    w=100*np.maximum(r[policy]["x"],0)
    ax.barh(y+shift,w,height=.32,color=color,label=label)
    for yy,ww in zip(y+shift,w):
        if ww>.05:ax.text(ww+.35,yy,f"{ww:.1f}%",va="center",fontsize=9)
ax.set_yticks(y,S.NAMES);ax.invert_yaxis();ax.set_xlim(0,40)
ax.set_xticks([0,10,20,30,40],["0%","10%","20%","30%","40%"])
ax.set_xlabel("Holding as a percentage of initial wealth")
ax.set_title("A diversified portfolio without position caps",loc="left",fontsize=15,pad=30)
ax.text(0,1.025,"From cash · risk aversion 2.5 · fund costs 5 bp · ETF costs 2 bp",transform=ax.transAxes,fontsize=10)
ax.axhline(5.5,color="#bbbbbb",linewidth=.8)
ax.grid(axis="x",alpha=.16);ax.set_axisbelow(True)
for spine in ("top","right","left"):ax.spines[spine].set_visible(False)
ax.tick_params(axis="y",length=0)
ax.legend(loc="lower right",frameon=False)
fig.text(.18,.015,f"Both policies: no borrowing. Planning gain: {r['gain_bp']:.2f} bp over two reviews.",fontsize=10)
fig.subplots_adjust(left=.18,right=.95,top=.84,bottom=.13)
outfig=S.HERE.parents[1]/"figures"
for ext in ("png","pdf"):fig.savefig(outfig/f"fig4_diversified.{ext}",dpi=180,bbox_inches="tight")
plt.close(fig)

b=T["baseline"]
lines=["# Diversification first, then the value of planning", "",
"This setting has a portfolio to construct: equity, duration and credit provide different return/risk tradeoffs, and several active funds and ETFs offer overlapping implementations. Diversification is chosen by the objective, without position caps or target allocation constraints. The additional gain from planning ahead is measured separately and remains modest in the baseline.", "",
"All inputs are illustrative assumptions. This is existing M9 on a six-fund, three-ETF menu, not an empirical calibration or a new theorem. The design was saved before computation in [DESIGN.md](DESIGN.md); the previous studies are preserved, not silently recalibrated.", "",
"## Why this is a portfolio problem", "",
"The three underlying exposure sleeves have quarterly excess means 1.20%, 0.30%, 0.60%, return SDs 8%, 3%, 4%, and correlations 0 for equity-duration, 0.4 for equity-credit and 0.2 for duration-credit, before ETF tracking residuals and mean uncertainty. The sleeve returns are therefore neither identical nor assumed mutually independent. Two active funds per sleeve have different factor tilts, uncertain small net alphas, and residual return risks. Their returns correlate through the shared factors; independent fund residuals remain an explicit simplifying assumption.", "",
"Net alpha estimates are (4,2,1,0.5,3,1) bp per quarter, with alpha prior SDs (20,30,10,15,15,25) bp. Unlike the old example, a large alpha advantage does not select one fund to supply every exposure. Manager-specific forecasts can reverse the ordering within each pair. Initial uncertainty and future state noise are distinct inputs; the uncertainty sensitivity changes the former only.", "",
"First remove investor trading costs to inspect the opportunity set itself, retaining ETF fees and predictive risk. Risk aversion is 2.5; all holdings are funded, long-only and uncapped:", "",
"| Static alternative | Portfolio or largest holding | Quarterly score |",
"|---|---|---:|",
f"| Best single instrument plus cash | {100*b['best_single']['weight']:.2f}% {b['best_single']['instrument']}, remainder cash | {b['best_single']['score_bp']:.2f} bp |",
f"| ETF-only optimum | Equity {100*b['etfs']['x'][6]:.2f}%, duration {100*b['etfs']['x'][7]:.2f}%, credit {100*b['etfs']['x'][8]:.2f}% | {b['etfs']['score_bp']:.2f} bp |",
f"| Full fund/ETF optimum | {b['full']['positions_above_1pct']} positions above 1%; largest {100*b['full']['max_weight']:.2f}% | {b['full']['score_bp']:.2f} bp |", "",
f"ETF diversification alone improves the quarterly score by {b['etfs']['score_bp']-b['best_single']['score_bp']:.2f} bp relative to the best single-instrument alternative. Allowing funds adds a further {b['full']['score_bp']-b['etfs']['score_bp']:.2f} bp. These are static comparisons; neither is a gain from planning ahead. The full optimum has expected quarterly excess return {b['full']['mean_bp']/100:.3f}% and predictive return SD {b['full']['sd_pct']:.3f}%.", "",
f"Across the 27 prespecified static cases (gamma 2–3; alpha means 0,1,2 times baseline; initial alpha uncertainty 0.5,1,2 times baseline), the full portfolio's score advantage over the best single instrument plus cash is at least {min(t['diversification_gain_bp'] for t in T['results']):.2f} bp. Its largest position never exceeds {100*max(t['full']['max_weight'] for t in T['results']):.2f}%. Those are observed outcomes, not imposed limits. An independently constructed covariance and SLSQP solve reproduce the baseline holdings within {T['independent_max_holding_difference']:.2g} of initial wealth.", "",
"## Actual construction with trading costs", "",
"Baseline costs are 5 bp per fund purchase/redemption and 2 bp per ETF purchase/sale. Fees remain 2,1,3 bp per quarter for the equity, duration and credit ETFs. Starting from cash, the current allocations are:", "",
"| Instrument | One-quarter | Plan ahead |",
"|---|---:|---:|"]
for i,name in enumerate(S.NAMES):lines.append(f"| {name} | {max(100*r['myopic']['x'][i],0):.2f}% | {max(100*r['dynamic']['x'][i],0):.2f}% |")
for label,key,scale in (("Cash","cash",100),("Today's costs","cost0_bp",.01)):
    lines.append(f"| {label} | {max(scale*r['myopic'][key],0):.2f}% | {max(scale*r['dynamic'][key],0):.2f}% |")
lines += ["", "![Actual uncapped holdings, from cash.](../../figures/fig4_diversified.png)", "",
f"One-quarter optimization holds {r['myopic']['funds_pct']:.2f}% in funds and {r['myopic']['etfs_pct']:.2f}% in ETFs; planning ahead holds {r['dynamic']['funds_pct']:.2f}% and {r['dynamic']['etfs_pct']:.2f}%. Both leave essentially zero cash. Planning gains {r['gain_bp']:.4f} bp in the two-review objective. The allocation changes are visible, but the gain is small: the objective values nearby implementations similarly. This is not evidence of a large investment-performance improvement.", "",
"## Starting holdings and forecast changes", "",
"All four starts have wealth one. The ETF and fund starts are equally weighted within their respective menus. The mixed start holds 40% funds, 55% ETFs and 5% cash, with instrument weights specified in the design. No portfolio gets free financing. Each policy sees the same returns and forecasts, uses the same linear filter, and respects every future budget. The one-quarter policy learns and reoptimizes; it omits continuation only when choosing today's action.", "",
"| Start, steady forecast | One-quarter funds / ETFs | Plan-ahead funds / ETFs | Planning gain |",
"|---|---:|---:|---:|"]
for start in S.STARTS:
    rr=base(start)
    lines.append(f"| {start} | {rr['myopic']['funds_pct']:.2f}% / {rr['myopic']['etfs_pct']:.2f}% | {rr['dynamic']['funds_pct']:.2f}% / {rr['dynamic']['etfs_pct']:.2f}% | {rr['gain_bp']:.4f} bp |")
lines += ["", "The manager-rotation forecast swaps each pair's next-review alpha means, so it does not preserve the same manager ranking forever. The premium rotation lowers the equity-sleeve premium by 15 bp and raises duration's by 5 bp while keeping credit's unchanged; the reverse forecast changes those signs. These are specified forecasts, not estimates of predictability. All use the same persistence and state-noise variances.", "",
"| Forecast | From cash | From ETFs | From funds | From mixed |",
"|---|---:|---:|---:|---:|"]
for forecast in ("steady","manager_rotation","premium_rotation","premium_reverse"):
    lines.append("| "+forecast+" | "+" | ".join(f"{base(st,forecast)['gain_bp']:.4f} bp" for st in S.STARTS)+" |")
lines += ["", "## Full sensitivity and scope", "",
"The 80 core cases cross the four starts and four forecasts with alpha uncertainty scales 0.5,1,2 at gamma 2.5 and gamma 2,3 at baseline uncertainty. The 64 cost cases separately vary fund costs to 0 or 20 bp and ETF costs to 0 or 5 bp, keeping other baseline inputs. These are planned sensitivities, not a random sample.", "",
"| Block | Cases | Median planning gain | Maximum planning gain | Cases above 1 bp |",
"|---|---:|---:|---:|---:|"]
for name in ("core","costs","all"):
    a=summary[name];lines.append(f"| {name} | {a['n']} | {a['median']:.4f} bp | {a['maximum']:.4f} bp | {a['above_1']} |")
mx=summary["maximum_case"]
lines += ["",f"The grid maximum is {mx['gain_bp']:.4f} bp: start `{mx['start']}`, forecast `{mx['forecast']}`, gamma {mx['gamma']:g}, alpha-uncertainty scale {mx['uncertainty']:g}, fund cost {mx['fund_bp']:g} bp and ETF cost {mx['etf_bp']:g} bp. It is reported as an extremum, not selected as the headline case.", "",
f"Across all 144 dynamic comparisons and both policies, at least {summary['all']['minimum_positions']} instruments have positions above 1%, and the largest position is {100*summary['all']['max_weight']:.2f}% of initial wealth. The setting supports diversified portfolios without mechanically fixing their composition. Factor exposure units need not sum to 100% because fund loadings differ from one; capital weights plus cash and costs do, and no investor leverage is allowed.", "",
"The interpretation is narrower than a claim that dynamics are always important: the opportunity set supports ordinary diversification; funds and ETFs supply different implementations; anticipation can change their mixture, but the incremental objective gains must be reported on their own scale. The static diversification calculation is standard portfolio mathematics, not a new research theorem. The dynamic solver instantiates the existing funded model, not a new algorithm. No result establishes empirical performance, optimal long-run weights, a stationary attractor, or the superiority of the linear filter to a true posterior.", "",
"Remaining assumptions include known loadings and return covariances, independent active residuals conditional on factors, small assumed alpha forecasts, assumed investor costs, and a two-review additive mean-variance objective. This is a coherent illustrative portfolio construction problem; it is not a calibrated real-world fund selection exercise.", "",
"## Verification and reproduction", "",
f"All 144 joint solves returned optimal status. Recorded warnings: {summary['warnings']}. Maximum reconstructed objective error: {summary['max_objective_error']:.3g}; most negative reconstructed cash: {summary['min_cash']:.3g}, within numerical tolerance. A separate implementation constructs the state law, diagonal filter and vectorized QPs independently of the lab's tree and solver. It reproduces the eight baseline steady/manager-rotation cases with maximum gain difference {max(c['gain_difference_bp'] for c in checks):.3g} bp and maximum holding difference {max(c['max_holding_difference'] for c in checks):.3g}. No formal source was changed.", "",
"```bash", ".venv/bin/python manuscript2/analysis/diversified/static.py", ".venv/bin/python manuscript2/analysis/diversified/run.py", ".venv/bin/python manuscript2/analysis/diversified/verify.py", ".venv/bin/python manuscript2/analysis/diversified/report.py", "```", "",
"[results.csv](results.csv) contains every dynamic case; [results.json](results.json) includes holdings, costs, state details for baseline cases and source/environment metadata. [static_results.json](static_results.json) records all 27 construction checks. [verification.json](verification.json), [verification_comparison.json](verification_comparison.json) and [summary.json](summary.json) contain the independent results and summaries.", ""]
(S.HERE/"REPORT.md").write_text("\n".join(lines))
print(json.dumps({k:v for k,v in summary.items() if k!='maximum_case'},indent=2))
print('Maximum case', {k:mx[k] for k in ('gain_bp','start','forecast','gamma','uncertainty','fund_bp','etf_bp')})
