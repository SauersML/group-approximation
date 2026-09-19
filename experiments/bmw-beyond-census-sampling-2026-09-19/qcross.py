# qcross.py: independent check of qsphere.py. Builds the whole BMW group Gamma = <h, v | squares> in GAP,
# its parity kernel Gamma^+ (index 4), and the quotient of Gamma^+ by the normal closure (in Gamma^+) of B^+
# (resp. A^+), with no use of the automaton actions or of Steps 3-4. Prints the abelian invariants.
# usage: qcross.py pattern idx side      (side B: kill B^+, compare with QB; side A: kill A^+, compare with QA)
import sys, subprocess, os
D = '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17'; sys.path.insert(0, D)
from lo_census import load
pat, idx, side = sys.argv[1], int(sys.argv[2]), sys.argv[3]
G = dict(load(os.path.join(D, 'census_%s.json' % pat)))[idx]
m, n = G.m, G.n
def gen(t, x):
    inv = G.iA if t == 'h' else G.iB; off = 0 if t == 'h' else m
    return 'f[%d]' % (off + x + 1) if inv[x] >= x else 'f[%d]^-1' % (off + inv[x] + 1)
rels = ['f[%d]^2' % (x + 1) for x in range(m) if G.iA[x] == x] + ['f[%d]^2' % (m + x + 1) for x in range(n) if G.iB[x] == x]
rels += ['%s*%s*(%s*%s)^-1' % (gen('h', h), gen('v', v), gen('v', v2), gen('h', h2)) for (h, v), (v2, h2) in G.SQ.items()]
inv = G.iB if side == 'B' else G.iA; t = 'v' if side == 'B' else 'h'; L = n if side == 'B' else m
kill = ['%s*%s' % (gen(t, x), gen(t, y)) for x in range(L) for y in range(L) if y != inv[x]]
code = ('F:=FreeGroup(%d);; f:=GeneratorsOfGroup(F);; Gm:=F/[%s];; g:=GeneratorsOfGroup(Gm);;\n'
        'hom:=GroupHomomorphismByImages(Gm,Group((1,2),(3,4)),g,Concatenation(List([1..%d],i->(1,2)),List([1..%d],i->(3,4))));;\n'
        'K:=Kernel(hom);; iso:=IsomorphismFpGroup(K);; P:=Range(iso);; FP:=FreeGroupOfFpGroup(P);;\n'
        'e:=w->MappedWord(w,GeneratorsOfGroup(F),g);;\n'
        'R:=Concatenation(RelatorsOfFpGroup(P),List([%s],w->UnderlyingElement(Image(iso,e(w)))));;\n'
        'Print("XRES ",Index(Gm,K)," ",AbelianInvariants(FP/R),"\\n");\nQUIT;\n'
        % (m + n, ','.join(rels), m, n, ','.join(kill)))
p = subprocess.run(['timeout', '600', 'gap', '-q', '-b'], input=code, capture_output=True, text=True)
print(pat, idx, side, [l for l in p.stdout.split('\n') if l.startswith('XRES')] or p.stderr[-300:])
