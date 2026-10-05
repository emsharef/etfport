"""Standalone reproduction entry points; no local lab configuration is required."""
from pathlib import Path
import argparse,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
R=ROOT/'research'

def run(script,*args,cwd=ROOT):
    subprocess.run([sys.executable,str(script),*args],cwd=cwd,check=True)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('target',choices=['examples','figures','verify','analysis','papers'])
    args=parser.parse_args()
    if args.target=='examples':
        from etfport import compare_policies
        from etfport.examples import make_example
        import json
        out=ROOT/'build/examples';out.mkdir(parents=True,exist_ok=True)
        for scenario in ('premium_down_persistent','alpha_up','alpha_down','style_up','style_down'):
            r=compare_policies(make_example(scenario))
            (out/f'{scenario}.json').write_text(json.dumps(r.to_dict(),indent=2)+'\n')
            print(scenario,f'{r.planning_gain_bp:.6f} score bp',flush=True)
    elif args.target=='figures':
        run(R/'manuscript2/make_figures.py',cwd=R)
        run(R/'manuscript2/analysis/forecast_extension/report.py',cwd=R)
        print('Regenerated research/manuscript2/figures; archived paper figures are preserved.')
    elif args.target=='verify':
        for name in ('forecast_revision','forecast_extension'):
            run(R/'manuscript2/analysis'/name/'verify.py',cwd=R)
        run(R/'manuscript2/analysis/review_round4/analyze.py',cwd=R)
    elif args.target=='analysis':
        for name in ('forecast_revision','forecast_extension'):
            run(R/'manuscript2/analysis'/name/'run.py',cwd=R)
            run(R/'manuscript2/analysis'/name/'verify.py',cwd=R)
            run(R/'manuscript2/analysis'/name/'report.py',cwd=R)
        run(R/'manuscript2/analysis/review_round4/analyze.py',cwd=R)
    elif args.target=='papers':
        for paper in ('manuscript','lab'):
            src=ROOT/'papers'/paper
            out=ROOT/'build/papers'/paper;out.mkdir(parents=True,exist_ok=True)
            subprocess.run(['tectonic','--outdir',str(out),str(src/'main.tex')],cwd=src,check=True)
        print('Built PDFs in build/papers; distributed paper.pdf files remain the preserved snapshots.')

if __name__=='__main__':main()
