"""Stage 2: existing funded M9 programs on the prespecified diversified menu."""
import csv,hashlib,itertools,json,multiprocessing as mp,platform,sys,time,warnings
from pathlib import Path
import numpy as np
import menu as S
sys.path.insert(0,str(S.ROOT/"experiments/d26-prep"))
import policies as P

FORECASTS=("steady","manager_rotation","premium_rotation","premium_reverse")
def cases():
    out=[]
    for (g,u),start,forecast in itertools.product(((2.5,.5),(2.5,1.),(2.5,2.),(2.,1.),(3.,1.)),S.STARTS,FORECASTS):
        out.append(dict(block="core",gamma=g,uncertainty=u,fund_bp=5.,etf_bp=2.,start=start,forecast=forecast))
    for (f,e),start,forecast in itertools.product(((0.,2.),(20.,2.),(5.,0.),(5.,5.)),S.STARTS,FORECASTS):
        out.append(dict(block="costs",gamma=2.5,uncertainty=1.,fund_bp=f,etf_bp=e,start=start,forecast=forecast))
    assert len(out)==144
    return [dict(case_id=i,**c) for i,c in enumerate(out)]

def evaluate(c):
    began=time.monotonic()
    with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter("always")
        M=S.build(**c);xm,hm=S.STARTS[c["start"]]
        D=M.solve(xm,hm);assert D["status"]=="optimal",D["status"]
        nodes=D["levels"][1];q=np.array([n["prob"] for n in nodes])
        assert min(n["g"].min() for n in nodes)>0
        mu,V=M.moments(0,M.m0)
        xmy,_,hmy=M.one_review(mu,V,xm,hm)
        my=P.tomorrow(M,nodes,xmy,hmy)
        rec={}
        detail=c["gamma"]==2.5 and c["uncertainty"]==1 and c["fund_bp"]==5 and c["etf_bp"]==2
        for name,x,tm in (("myopic",xmy,my),("dynamic",D["x"][0][0],None)):
            h=P.cash_after(M,hm,x,xm)
            if tm is None:
                tm=[]
                for k,nd in enumerate(nodes):
                    xx=D["x"][1][k];carried=nd["g"]*x;hh=P.cash_after(M,h,xx,carried)
                    assert abs(hh-D["h"][1][k])<2e-7
                    m,v=M.moments(1,nd["m"])
                    tm.append(dict(x1=xx,xm=carried,h=hh,eta=D["eta"][1][k],score=P.score(M,m,v,xx,carried)))
            assert min(x.min(),h,min(t["x1"].min() for t in tm),min(t["h"] for t in tm))>-2e-7
            c0=P.cost(M,x-xm)
            assert abs(x.sum()+h+c0-1)<1e-9
            for t in tm:
                assert abs(t["x1"].sum()+t["h"]+P.cost(M,t["x1"]-t["xm"])-t["xm"].sum()-h)<2e-7
            J=P.score(M,mu,V,x,xm)+float(q@[t["score"] for t in tm])
            d=np.array([t["x1"]-t["xm"] for t in tm])
            rec[name]=dict(x=x.tolist(),cash=float(h),J=J,funds_pct=float(100*x[:6].sum()),
                           etfs_pct=float(100*x[6:].sum()),cash_pct=float(100*h),sleeve_exposures=S.sleeves(x).tolist(),
                           cost0_bp=1e4*c0,expected_cost1_bp=1e4*float(q@[P.cost(M,t["x1"]-t["xm"]) for t in tm]),
                           mean0_bp=float(1e4*mu@x),sd0_pct=float(100*np.sqrt(x@V@x)),
                           max_weight=float(max(x)),positions_above_1pct=int(sum(x>.01)),
                           future_min_cash=float(min(t["h"] for t in tm)),
                           future_cash_price_probability=float(q@[t["eta"]>1e-8 for t in tm]),
                           expected_next_trade=(q@d).tolist())
            if detail:rec[name]["states"]=[dict(q=float(q[k]),x1=t["x1"].tolist(),trade=d[k].tolist(),
                                                cash=t["h"],eta=t["eta"]) for k,t in enumerate(tm)]
        err=rec["dynamic"]["J"]-D["value"];assert abs(err)<1e-8
        gain=(rec["dynamic"]["J"]-rec["myopic"]["J"])*1e4;assert gain>-1e-4
        out=dict(**c,**rec,gain_bp=gain,states=len(nodes),status=D["status"],
                  objective_error=err,warnings=[str(w.message) for w in caught],seconds=time.monotonic()-began)
        return out

def main():
    assert (S.HERE/"static_results.json").exists(),"Complete and inspect stage 1 first."
    done=[];began=time.monotonic()
    with (S.HERE/"cases.jsonl").open("w") as f,mp.get_context("spawn").Pool(4) as pool:
        for r in pool.imap_unordered(evaluate,cases()):
            done.append(r);f.write(json.dumps(r)+"\n");f.flush()
            if len(done)%8==0:print(f"{len(done)}/144; {time.monotonic()-began:.1f}s; latest gain {r['gain_bp']:.5f} bp",flush=True)
    done.sort(key=lambda r:r["case_id"])
    import cvxpy,clarabel
    paths=[S.HERE/f for f in ("DESIGN.md","menu.py","static.py","run.py")]+[S.ROOT/"experiments/d16-harness/harness_n.py",S.ROOT/"experiments/d26-prep/policies.py",S.ROOT/"uv.lock"]
    env=dict(python=platform.python_version(),platform=platform.platform(),numpy=np.__version__,cvxpy=cvxpy.__version__,clarabel=clarabel.__version__)
    out=dict(results=done,env=env,wall_seconds=time.monotonic()-began,
             source_hashes={str(p.relative_to(S.ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths})
    (S.HERE/"results.json").write_text(json.dumps(out,indent=2)+"\n")
    rows=[]
    for r in done:
        row={k:v for k,v in r.items() if k not in ("myopic","dynamic","warnings")}
        row["warning_count"]=len(r["warnings"])
        for name in ("myopic","dynamic"):
            for k,v in r[name].items():
                if not isinstance(v,list):row[name+"_"+k]=v
        rows.append(row)
    with (S.HERE/"results.csv").open("w",newline="") as f:
        w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)
    print("All 144 cases completed; numerical checks passed.",flush=True)

if __name__=="__main__":main()
