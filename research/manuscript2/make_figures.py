"""Decision-focused illustrations of existing results, with source hashes.

No new scenarios are optimized. Figure 1 evaluates the proved clipping rule at
an explicitly chosen incumbent using saved grid edges. Figure 3 selects each
shortcut's largest loss, normalized by initial wealth, from all 72 saved cases.
"""
from pathlib import Path
import hashlib
import json
import os
os.environ.setdefault('MPLCONFIGDIR','/tmp/manuscript2-matplotlib')
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

ROOT=Path(__file__).resolve().parents[1]
OUT=Path(__file__).resolve().parent/'figures'
OUT.mkdir(exist_ok=True)
NAVY,TEAL,ORANGE,GREY='#243b53','#177e89','#c46732','#8795a1'
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,
 'axes.spines.top':False,'axes.spines.right':False,'axes.edgecolor':'#c0c8ce',
 'axes.labelcolor':NAVY,'text.color':NAVY,'xtick.color':NAVY,'ytick.color':NAVY,
 'axes.titlesize':12,'axes.titleweight':'bold','pdf.fonttype':42,'savefig.facecolor':'white'})
manifest={'description':__doc__,'inputs':{}}
def read(rel):
 data=(ROOT/rel).read_bytes();manifest['inputs'][rel]=hashlib.sha256(data).hexdigest();return json.loads(data)
def save(fig,name):
 for ext in ['png','pdf']:fig.savefig(OUT/f'{name}.{ext}',dpi=200,bbox_inches='tight')
 plt.close(fig)

# Figure 1: hold versus sell at the same fund holding, beliefs and cost rates.
c=next(c for c in read('experiments/036/summary.json')['cells'] if c['corr']==.5
 and c['kA']==[.001,.001] and c['kE']==[.0002,.0002] and c['r']==0 and c['step']==.5 and c['hfac']==1)
terminal=c['rows'][-1];early=c['rows'][0];inc=.0335
fig,(ax,bx)=plt.subplots(1,2,figsize=(10,4.0),gridspec_kw={'width_ratios':[1.15,1]})
x=np.array([b['dE'] for b in terminal['bands']])*100
hi=np.array([b['hi'] for b in terminal['bands']])*100
ax.fill_between(x,1.8,hi,color=TEAL,alpha=.12)
ax.fill_between(x,hi,4.3,color=ORANGE,alpha=.10)
ax.plot(x,hi,color=TEAL,lw=2.5,label='Upper edge of fund hold band')
ax.axhline(inc*100,color=NAVY,ls='--',lw=1)
ax.text(-2.17,4.02,'SELL FUND',color=ORANGE,weight='bold')
ax.text(.45,2.60,'HOLD FUND',color=TEAL,weight='bold')
ax.text(-.25,3.43,'Same fund holding',fontsize=9,color=NAVY)
chosen=[min(terminal['bands'],key=lambda b:abs(b['dE']-v)) for v in [-.02,.02]]
for j,b in enumerate(chosen):
 xx=b['dE']*100;edge=b['hi']*100
 ax.plot(xx,inc*100,'o',color=NAVY,ms=6,zorder=5)
 if inc>b['hi']:
  ax.annotate('',(xx,edge),(xx,inc*100),arrowprops={'arrowstyle':'->','color':ORANGE,'lw':2})
  ax.text(xx-.1,2.96,'Sell to edge',ha='right',fontsize=9,color=ORANGE)
 else:ax.text(xx+.1,3.14,'Keep fund',fontsize=9,color=TEAL)
ax.set(xlim=(-2.25,2.25),ylim=(2.4,4.25),xlabel='ETF holding minus target (100 × dollars)',ylabel='Fund holding minus target (100 × dollars)')
ax.set_title('A  Changing the ETF can trigger a fund sale',loc='left',fontsize=11,pad=14)
# Evaluate clip at identical ETF coordinates via nearest saved grid node.
examples=[]
for b in chosen:
 for row,label in [(terminal,'Last date'),(early,'Eight dates left')]:
  z=min(row['bands'],key=lambda z:abs(z['dE']-b['dE']))
  sale=max(0,inc-z['hi'])*100
  examples.append(dict(horizon=label,etf_deviation=z['dE'],fund_deviation=inc,upper=z['hi'],sale=sale/100))
for j,color in enumerate([TEAL,NAVY]):
 vals=[examples[2*i+j]['sale']*100 for i in range(2)]
 bars=bx.bar(np.arange(2)+(j-.5)*.32,vals,width=.29,color=color,label=['Last date','Eight dates left'][j])
 for bar,v in zip(bars,vals):bx.text(bar.get_x()+bar.get_width()/2,v+.035,'Hold' if v<1e-9 else f'{v:.2f}',ha='center',fontsize=9)
bx.set(xticks=[0,1],xticklabels=['ETF below target','ETF above target'],ylabel='Fund sale (100 × dollars)',ylim=(0,1.52))
bx.set_title('B  Planning horizon also changes the trade',loc='left',fontsize=11,pad=14)
bx.legend(frameon=False,loc='upper left',fontsize=9)
bx.grid(axis='y',alpha=.12);bx.set_axisbelow(True)
fig.tight_layout(w_pad=2.0);save(fig,'fig1_bands')
manifest['figure1']={'source_cell':{k:v for k,v in c.items() if k!='rows'},'incumbent_fund_deviation':inc,'examples':examples,'note':'Panel A shows only the upper boundary, not the purchase boundary. Panel B uses nearest saved grid ETF coordinates; exact coordinates recorded here.'}

# Figure 2: plot trades rather than hiding them inside total holdings.
w=read('experiments/050/summary.json');a=w['t5']['A'];b=w['t5']['B']
root=np.array(w['t4']['dynamic']);cash=max(w['t4']['cash_after'],0)
trades=[[*list(root-np.array([.4,0])),cash-.06],
 [*list(np.array(a['x1'])-np.array(a['marked'])),0],
 [*list(np.array(b['x1'])-np.array(b['marked'])),0]]
assert abs(trades[2][0]*1.005+trades[2][1]*.999)<1e-7
fig,axes=plt.subplots(1,3,figsize=(10,3.9),sharey=True)
titles=['A  Today: buy ETF','B  Tomorrow, state A: hold','C  Tomorrow, state B: switch']
for j,ax in enumerate(axes):
 vals=np.array(trades[j])*100
 ax.bar([0,1,2],vals,color=[NAVY,TEAL,GREY],width=.55)
 ax.axhline(0,color=GREY,lw=.8)
 for k,v in enumerate(vals):
  text='0' if abs(v)<1e-5 else f'{v:+.3f}'
  ax.text(k,v+(.35 if v>=-1e-5 else -.35),text,ha='center',va='bottom' if v>=-1e-5 else 'top',fontsize=10)
 ax.set_xticks([0,1,2],['Fund','ETF','Cash']);ax.set_ylim(-9.5,10)
 ax.set_title(titles[j],loc='left',fontsize=10.5,pad=12)
 ax.grid(axis='y',alpha=.12);ax.set_axisbelow(True)
 ax.text(.5,.95,['Use the 0.06 cash balance','No trade despite revised estimates','ETF sale pays for fund purchase'][j],transform=ax.transAxes,ha='center',va='top',fontsize=8.5)
axes[0].set_ylabel('Change at the trading date (100 × dollars)')
fig.tight_layout(w_pad=1.3);save(fig,'fig2_worked')
manifest['figure2']={'trades':trades,'marked_state_A':a['marked'],'marked_state_B':b['marked'],'sale_net_proceeds':-trades[2][1]*.999,'purchase_including_cost':trades[2][0]*1.005}
manifest['posterior_comparison']={'gain_wealth_bp':1e4*(w['t6']['exact_dynamic']-w['t6']['filter_dynamic'])/.46,'different_nodes':w['t6']['nodes_differ_dynamic']}

# Figure 3: show the allocation behind each shortcut's largest normalized loss.
analysis=read('manuscript2/figures/policy_analysis.json');rows=analysis['cells']
source=read('experiments/048/summary.json')['cells']
assert analysis['source_sha256']==manifest['inputs']['experiments/048/summary.json']
selected=[max(rows,key=lambda r:r[p]['loss_wealth_bp']) for p in ['myopic','ef111']]
fig,axes=plt.subplots(1,2,figsize=(10,4.8),sharey=True)
for j,(ax,r) in enumerate(zip(axes,selected)):
 wealth=r['initial_wealth'];holdings=[]
 for policy in ['dynamic','myopic','ef111']:
  x=np.array(r[policy]['x0']);u=x-np.array(r['start']);C=r['fund_rate']*abs(u[0])+r['etf_rate']*abs(u[1])
  h=max(0,r['cash']-sum(u)-C);holdings.append([*x,h])
 holdings=np.array(holdings)*100/wealth;bottom=np.zeros(3)
 for k,(color,label) in enumerate([(NAVY,'Fund'),(TEAL,'ETF'),(GREY,'Cash')]):
  ax.bar(np.arange(3),holdings[:,k],bottom=bottom,width=.52,color=color,label=label)
  for i,v in enumerate(holdings[:,k]):
   if v>9:ax.text(i,bottom[i]+v/2,f'{v:.1f}%',ha='center',va='center',color='white',weight='bold',fontsize=10)
  bottom+=holdings[:,k]
 ax.set_xticks(np.arange(3),['Dynamic','Myopic','Exposure first']);ax.set_ylim(0,111)
 ax.set_title(['A  Planning ahead: sell more ETF now','B  Exact exposure prevents a fund switch'][j],loc='left',fontsize=11,pad=30)
 ax.text(0,1.02,['Start: ETF 0.9; cash 0.005','Start: fund 0.15; cash 0.005'][j],transform=ax.transAxes,fontsize=9)
 ax.grid(axis='y',alpha=.12);ax.set_axisbelow(True)
 for i,policy in enumerate(['dynamic','myopic','ef111']):
  p=r[policy];ax.text(i,-.15,f"{max(0,p['loss_wealth_bp']):.2f}",transform=ax.get_xaxis_transform(),ha='center',fontsize=10,weight='bold')
  ax.text(i,-.23,f"{p['cost_total_wealth_bp']:.2f}",transform=ax.get_xaxis_transform(),ha='center',fontsize=10)
 ax.text(-.02,-.32,'Rows below: objective loss / trading cost (bp of initial wealth)',transform=ax.transAxes,fontsize=8)
axes[0].set_ylabel('Allocation today (% of initial wealth)')
handles,labels=axes[0].get_legend_handles_labels()
fig.legend(handles,labels,loc='lower center',ncol=3,frameon=False,bbox_to_anchor=(.5,-.045))
fig.subplots_adjust(left=.075,right=.99,top=.86,bottom=.28,wspace=.23)
save(fig,'fig3_policy_losses')
loss_my=np.array([r['myopic']['loss_wealth_bp'] for r in rows]);loss_ef=np.array([r['ef111']['loss_wealth_bp'] for r in rows])
metrics={'cells':72,'wealth_range':[min(r['initial_wealth'] for r in rows),max(r['initial_wealth'] for r in rows)],
 'myopic_max_loss_wealth_bp':float(loss_my.max()),'exposure_first_max_loss_wealth_bp':float(loss_ef.max()),
 'myopic_below_0.01_wealth_bp':int(sum(loss_my<.01)),'exposure_first_below_0.01_wealth_bp':int(sum(loss_ef<.01)),
 'myopic_exact_classification':sum(r['myopic_exact'] for r in rows),
 'myopic_inexact_below_0.0001_wealth_bp':sum(not r['myopic_exact'] and r['myopic']['loss_wealth_bp']<.0001 for r in rows),
 'binding_cells':sum(r['binding'] for r in rows),'binding_max_myopic_loss_wealth_bp':max(r['myopic']['loss_wealth_bp'] for r in rows if r['binding'])}
manifest['figure3']={'selection':'Maximum loss divided by initial wealth for each shortcut, over the entire registered grid; cases are diagnostic, not typical. Panel B has an essentially singleton second-stage feasible set under the exact exposure equality.','selected_case_indices':[r['index'] for r in selected],'metrics':metrics}
diagnostics=read('manuscript2/figures/round2_diagnostics.json')
for rel,digest in diagnostics['inputs'].items():
 assert hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()==digest, f'Stale round-2 diagnostics: {rel}'
manifest['round2_diagnostics']={k:diagnostics[k] for k in ['summary','figure3A','figure3B']}
(OUT/'data_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(metrics,indent=2))
