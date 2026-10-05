"""Check publishable contents, source integrity, links and numerical summaries."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[1]

def main():
    guides=list(ROOT.glob('*.md'))+list((ROOT/'docs').glob('*.md'))+list((ROOT/'papers').glob('*/README.md'))
    for p in guides:
        for dest in re.findall(r'\]\(([^)]+)\)',p.read_text()):
            if '://' in dest or dest.startswith(('#','mailto:')):continue
            assert (p.parent/dest.split('#')[0]).exists(),f'Broken link {p}: {dest}'
    source=json.loads((ROOT/'docs/source-snapshot.json').read_text())
    assert len({r['path'] for r in source['files']})==len(source['files'])
    checked=0
    for r in source['files']:
        p=ROOT/r['path']
        assert p.exists(),p
        if r['path'].startswith(('lean/','papers/')) or p.suffix=='.py':
            assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'],f'Archived source changed: {p}'
            checked+=1
    for folder in ('manuscript','lab'):
        base=ROOT/'papers'/folder
        assert (base/'paper.pdf').read_bytes().startswith(b'%PDF')
        text=(base/'main.tex').read_text()
        for name in re.findall(r'\\includegraphics(?:\[[^\]]*\])?\{([^}]+)\}',text):
            assert (base/name).exists(),f'Missing TeX graphic: {name}'
    for name in ('board','agents','ops','.claude','.codex','.env','refs/text'):
        assert not (ROOT/name).exists(),f'Internal/private files in release: {name}'
    for p in (ROOT/'lean').rglob('*.lean'):
        if '.lake' in p.parts:continue
        text=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S)
        text=re.sub(r'--[^\n]*','',text)
        text=re.sub(r'"(?:\\.|[^"\\])*"','',text)
        assert not re.search(r'\b(sorry|admit|axiom)\b',text),f'Unfinished formal source: {p}'
    for name,expected in [('forecast_revision',108),('forecast_extension',49)]:
        rows=json.loads((ROOT/'research/manuscript2/analysis'/name/'results.json').read_text())['results']
        assert len(rows)==expected
        for r in rows:
            assert abs(r['gain_bp']-(r['dynamic']['value_bp']-r['myopic']['value_bp']))<1e-8
            assert abs(r['current_fund_permission_gain_bp']-(r['myopic']['score0_bp']-r['etf_only']['score0_bp']))<1e-8
            for policy in ('myopic','dynamic','etf_only'):
                a=r[policy];W=sum(r['initial_x'])+r['initial_cash']
                assert abs(sum(a['x'])+a['cash']+a['cost0_bp']/1e4-W)<1e-8
    print(f'Package checked: {len(guides)} guides, {checked} unchanged source files, both PDFs, and 157 numerical cases.')

if __name__=='__main__':main()
