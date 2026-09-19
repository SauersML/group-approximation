# qsphere.py: the quotients Q_B = Gamma^+/N_B = A^+/M and Q_A = Gamma^+/N_A = B^+/M' of the parity kernel by
# the normal closure of a vertex group, for the irreducible candidates of the census (and of the samples).
# M = <<a^-1 (beta.a)>>, and it is enough to take |a| = 2 and beta among the length-2 generators of B^+.
# If B^+ is transitive on the 2-sphere S_2(T_A) and m >= 3, then Q_B = 1 (proof in the route); otherwise Q is
# computed with GAP (Reidemeister-Schreier for the even subgroup, then coset enumeration with a limit).
# usage: qsphere.py pattern...     (e.g. qsphere.py 40_40 50_30)   prints one JSON line per candidate class
import sys, json, subprocess, os
D = '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17'; sys.path.insert(0, D)
from lo_census import load

def words2(inv, L):
    return [(x, y) for x in range(L) for y in range(L) if y != inv[x]]

def orbits(G, side):
    # side 'B': B^+ acting on S_2(T_A); b.a = a' where b a = a' b', read from rw(a^-1 b^-1) = b'^-1 a'^-1
    # side 'A': A^+ acting on S_2(T_B); a.b = b' where a b = b' a', read from rw(a b)
    iA, iB = G.iA, G.iB
    if side == 'A':
        pts = words2(iB, G.n); gens = words2(iA, G.m)
        def act(g, p):
            w = G.rw([('h', g[0]), ('h', g[1]), ('v', p[0]), ('v', p[1])])
            return tuple(c[1] for c in w if c[0] == 'v')
    else:
        pts = words2(iA, G.m); gens = words2(iB, G.n)
        def act(g, p):
            w = G.rw([('h', iA[p[1]]), ('h', iA[p[0]]), ('v', iB[g[1]]), ('v', iB[g[0]])])
            h = [c[1] for c in w if c[0] == 'h']; return (iA[h[1]], iA[h[0]])
    seen = {}; orbs = []
    for p in pts:
        if p in seen: continue
        o = [p]; seen[p] = len(orbs); i = 0
        while i < len(o):
            for g in gens:
                q = act(g, o[i])
                assert len(q) == 2
                if q not in seen: seen[q] = len(orbs); o.append(q)
            i += 1
        orbs.append(o)
    return orbs, (G.m if side == 'B' else G.n), (iA if side == 'B' else iB)

def gap_q(orbs, inv):
    L = len(inv); rep = [x for x in range(L) if inv[x] >= x]; gi = {x: i for i, x in enumerate(rep)}
    def gw(x): return 'f[%d]' % (gi[x] + 1) if x in gi else 'f[%d]^-1' % (gi[inv[x]] + 1)
    rel = ['f[%d]^2' % (gi[x] + 1) for x in rep if inv[x] == x]
    pairs = ['[%s*%s, %s*%s]' % (gw(o[0][0]), gw(o[0][1]), gw(p[0]), gw(p[1])) for o in orbs for p in o[1:]]
    return ('F:=FreeGroup(%d);; f:=GeneratorsOfGroup(F);; Ag:=F/[%s];; g:=GeneratorsOfGroup(Ag);;\n'
            'hom:=GroupHomomorphismByImages(Ag,Group((1,2)),g,List(g,x->(1,2)));; K:=Kernel(hom);;\n'
            'iso:=IsomorphismFpGroup(K);; P:=Range(iso);; FP:=FreeGroupOfFpGroup(P);;\n'
            'e:=w->MappedWord(w,GeneratorsOfGroup(F),g);;\n'
            'R:=Concatenation(RelatorsOfFpGroup(P),List([%s],p->UnderlyingElement(Image(iso,e(p[1])))^-1*UnderlyingElement(Image(iso,e(p[2])))));;\n'
            'Q:=FP/R;; ab:=AbelianInvariants(Q);; ct:=CosetTableFromGensAndRels(GeneratorsOfGroup(FP),R,[]:max:=200000,silent:=true);;\n'
            'if ct=fail then sz:=-1; else sz:=Length(ct[1]); fi;; Print("QRES ",ab," ",sz,"\\n");\n'
            % (L and len(rep), ','.join(rel), ','.join(pairs)))

def q_prog(G, side, tag):
    orbs, deg, inv = orbits(G, side)
    if len(orbs) == 1 and deg >= 3: return dict(orbits=[1], Q='1 (transitive)'), ''
    body = gap_q(orbs, inv).replace('Print("QRES ",', 'Print("QRES %s ",' % tag)
    return dict(orbits=sorted(len(o) for o in orbs), Q=None), body

if __name__ == '__main__':
    # one GAP session per pattern; each class is one block of the script
    for pat in sys.argv[1:]:
        outs = [json.loads(l) for l in open(os.path.join(D, 'out_%s.jsonl' % pat))]
        cand = {r['idx'] for r in outs if r['finH'] is None or r['finV'] is None}
        recs = {}; prog = []
        for i, G in load(os.path.join(D, 'census_%s.json' % pat)):
            if i not in cand: continue
            rec = dict(pat=pat, idx=i)
            for side in 'BA':
                rec['Q' + side], b = q_prog(G, side, '%d_%s' % (i, side)); prog.append(b)
            recs[i] = rec
        if any(prog):
            p = subprocess.run(['timeout', '3000', 'gap', '-q', '-b', '-o', '2g'], input=''.join(prog) + 'QUIT;\n',
                               capture_output=True, text=True)
            for l in p.stdout.split('\n'):
                if l.startswith('QRES'):
                    t, rest = l[5:].split(' ', 1); i, side = t.split('_'); recs[int(i)]['Q' + side]['Q'] = rest.strip()
        for i in sorted(recs): print(json.dumps(recs[i])); sys.stdout.flush()
