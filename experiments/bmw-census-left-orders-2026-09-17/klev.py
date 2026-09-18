import sys, itertools
sys.path.insert(0,'.')
from lo_census import load
from selfrep import build, act_path
from sympy.combinatorics import Permutation, PermutationGroup
idx=int(sys.argv[1]); side=sys.argv[2]; R=int(sys.argv[3])
G=next(G for i,G in load('census_40_40.json') if i==idx)
K=build(G,side); print('f',K['f'],'X',K['X'])
for a in range(K['nL']): print(a,[ (K['out'][(a,l)],K['sec'][(a,l)]) for l in K['X']])
for r in range(1,R+1):
    S=list(itertools.product(K['X'],repeat=r)); ix={w:i for i,w in enumerate(S)}
    P=PermutationGroup([Permutation([ix[act_path(K,(a,),w)[0]] for w in S]) for a in range(K['nL'])])
    print(r,P.order(),flush=True)
