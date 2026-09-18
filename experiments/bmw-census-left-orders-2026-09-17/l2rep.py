# Exact self-replication test for a subgroup H = <h_1..h_k> of the invariant-subtree group K (selfrep.build).
# If every h_i equals exactly (selfrep.trivial) the section at v of some word of H fixing v, then
# H <= phi_v(Stab_H(v)); with H moving v this makes H infinite (weak cycle lemma, kltc.py header), so Gamma is
# irreducible.  Words of H are enumerated to radius RH in the h_i^{+-1}, deduplicated by their action on level NL,
# so a failure is not a proof that no expression exists.
# usage (from this directory): l2rep.py idx side v L NL RH h_1,h_2,...   (words dot-separated; census_40_40.json)
#   L: radius of the K-ball used to report |phi_v(Stab_K(v))| mod level NL (0 skips it)
import sys, itertools
from lo_census import load
from selfrep import build, act_path, trivial, inv, act
from kkps import red
from sympy.combinatorics import Permutation, PermutationGroup
idx=int(sys.argv[1]); side=sys.argv[2]; v=int(sys.argv[3]); L=int(sys.argv[4]); NL=int(sys.argv[5])
G=next(G for i,G in load('census_40_40.json') if i==idx); K=build(G,side)
nL=K['nL']
Vx=list(itertools.product(K['X'],repeat=NL)); ix={x:i for i,x in enumerate(Vx)}
def perm(w): return tuple(ix[act_path(K,w,x)[0]] for x in Vx)
def words(gens, L):
    fr=[()]; seen={perm(()):()}
    out=[()]
    for _ in range(L):
        nf=[]
        for w in fr:
            for g in gens:
                w2=red(K,w+g); p=perm(w2)
                if p not in seen: seen[p]=w2; nf.append(w2); out.append(w2)
        fr=nf
    return out, seen
gens=[(a,) for a in range(nL)]
ws,_=words(gens,L) if L>0 else ([()],None)
print('ball',len(ws),flush=True)
secs={}
for w in ws:
    y,s=act_path(K,w,(v,))
    if y==(v,):
        s=red(K,s); p=perm(s)
        if p not in secs or len(s)<len(secs[p]): secs[p]=s
S=sorted(secs.values(),key=lambda s:(len(s),s))
print('distinct sections (mod level %d)'%NL,len(S),flush=True)
Gall=PermutationGroup([Permutation(list(perm(s))) for s in S]); print('order phi(Stab) mod level',Gall.order(), 'K mod level', PermutationGroup([Permutation(list(perm(g))) for g in gens]).order())
H=[tuple(map(int,w.split('.'))) for w in sys.argv[7].split(',')]
o=PermutationGroup([Permutation(list(perm(t))) for t in H]).order()
print('H gens',H,'order',o,flush=True)
Hgens=H+[inv(K,h) for h in H]
hw,_=words(Hgens,int(sys.argv[6]))
print('H ball',len(hw),flush=True)
orbit=set(act_path(K,w,(v,))[0] for w in hw); print('H orbit of v',orbit)
found={}
bysec={}
for w in hw:
    y,s=act_path(K,w,(v,))
    if y==(v,):
        s=red(K,s); bysec.setdefault(perm(s),[]).append((w,s))
for h in H:
    for w,s in bysec.get(perm(h),[]):
        if trivial(K,red(K,s+inv(K,h))): found[h]=w; break
print('exact expressions found',len(found),'of',len(H))
for h in H: print(h, '<-', found.get(h))
