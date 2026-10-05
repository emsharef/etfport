"""Command-line entry point for examples and user-supplied allocation problems."""
import argparse,json
from pathlib import Path
from .examples import SCENARIOS,make_example
from .io import load_problem
from .solver import compare_policies,solve_one_review,solve_two_review,SolverError


def main():
    parser=argparse.ArgumentParser(description='Funded allocation across funds and ETFs. Scores are not realized returns.')
    sub=parser.add_subparsers(dest='command',required=True)
    demo=sub.add_parser('example',help='Run one of the manuscript\'s assumed examples')
    demo.add_argument('--scenario',choices=SCENARIOS,default='premium_down_persistent')
    demo.add_argument('--output',type=Path)
    solve=sub.add_parser('solve',help='Solve an explicit JSON input')
    solve.add_argument('input',type=Path);solve.add_argument('--horizon',choices=['one','two','compare'],default='compare')
    solve.add_argument('--output',type=Path)
    args=parser.parse_args()
    try:
        P=make_example(args.scenario) if args.command=='example' else load_problem(args.input)
        mode='compare' if args.command=='example' else args.horizon
        result={'one':solve_one_review,'two':solve_two_review,'compare':compare_policies}[mode](P)
        data=result.to_dict();data['names']=list(P.names)
        data['scenario_labels']=[z.label for z in P.scenarios]
        data['assumed_example']=args.command=='example'
        if args.output:
            args.output.parent.mkdir(parents=True,exist_ok=True)
            args.output.write_text(json.dumps(data,indent=2,allow_nan=False)+'\n')
        if mode=='compare':
            print(f"{'Instrument':<16} {'Held':>10} {'One-review trade':>18} {'Planning trade':>17}")
            for name,held,one,plan in zip(P.names,P.portfolio.holdings,result.one_review.current.trades,result.planning.current.trades):
                values=[100*v/P.portfolio.wealth for v in (held,one,plan)]
                a,b,c=[0. if abs(v)<.005 else v for v in values]
                print(f'{name:<16} {a:>9.2f}% {b:>17.2f}% {c:>16.2f}%')
            benefit=0. if abs(result.current_fund_benefit_bp)<.0000005 else result.current_fund_benefit_bp
            print(f'Current fund-trading benefit: {benefit:.6f} score bp')
            print(f'Two-review planning gain:    {result.planning_gain_bp:.6f} score bp')
            print('Percentages use initial wealth. Score differences already deduct costs; they are not realized returns.')
        else:print(json.dumps(data,indent=2,allow_nan=False))
        if args.output:print(f'Saved {args.output}')
    except (ValueError,KeyError,OSError,SolverError,json.JSONDecodeError) as exc:
        parser.exit(2,f'etfport: {exc}\n')

if __name__=='__main__':main()
