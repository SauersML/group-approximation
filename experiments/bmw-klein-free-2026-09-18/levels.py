import sys, json
from sympy.combinatorics import Permutation, PermutationGroup
C='/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17/'
f, ci, N, SW = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), '--swap' in sys.argv
D=json.load(open(C+f)); m,n,iA,iB=D['m'],D['n'],D['iA'],D['iB']
SQ={tuple(a):tuple(b) for a,b in D['reps'][ci]}
VH={}
for (h,v),(v2,h2) in SQ.items(): VH[(iB[v2],h)]=(h2,iB[v])
# h acting on v-words: h v = v' h'
if not SW: T,nb,ilB,na=SQ,n,iB,m   # letters c (h) act on words of family v
else: T,nb,ilB,na=VH,m,iA,n
def act(c,w):
    out=[]
    for x in w:
        x2,c=T[(c,x)]; out.append(x2)
    return tuple(out)
for L in range(1,N+1):
    W=[()]
    for _ in range(L): W=[w+(x,) for w in W for x in range(nb) if not w or w[-1]!=ilB[x]]
    ix={w:i for i,w in enumerate(W)}
    gens=[Permutation([ix[act(c,w)] for w in W]) for c in range(na)]
    G=PermutationGroup(gens); o=G.order()
    print(L,len(W),o,flush=True)
