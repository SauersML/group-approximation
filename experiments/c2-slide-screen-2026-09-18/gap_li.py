# For JSON-line slide groups: count subgroups of index <= IDX in GAP (G = <x,y|w> has 4, 8, 16, 24
# for index <= 2..5) and report GAP's Tietze simplification.  Usage: gap_li.py file.jsonl IDX
import sys, json, subprocess, tempfile, os
def gw(u): return '*'.join({'x':'x','X':'x^-1','y':'y','Y':'y^-1','t':'t','T':'t^-1'}[c] for c in u)
src, idx = sys.argv[1], int(sys.argv[2])
for line in open(src):
    v = json.loads(line)
    prog = ('F:=FreeGroup("x","y","t");; x:=F.1;; y:=F.2;; t:=F.3;;\nGam:=F/[%s,%s];;\n' % (gw(v['R0']), gw(v['R1'])) +
            'Print(List([2..%d], n->Length(LowIndexSubgroupsFpGroup(Gam,n))), "\\n");\n' % idx +
            'P:=PresentationFpGroup(Gam);; TzOptions(P).printLevel:=0;; TzGoGo(P);;\n'
            'Print(Length(GeneratorsOfPresentation(P)), " gens, relator lengths ", List(RelatorsOfFpGroup(FpGroupPresentation(P)), Length), "\\n");\nQUIT;\n')
    with tempfile.NamedTemporaryFile('w', suffix='.g', delete=False) as fh: fh.write(prog)
    out = subprocess.run(['gap', '-q', '-o', '2g', fh.name], capture_output=True, text=True, timeout=1200).stdout
    os.unlink(fh.name)
    print(v['mode'], v['seed'], v['var'], v['sgn'], ' | '.join(out.strip().splitlines()), flush=True)
