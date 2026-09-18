# aut.py agrees with selfrep.build (experiments/bmw-census-left-orders-2026-09-17) for #332 and #193, both sides.
# Run from this directory; letters X are renumbered 0,1,2 in increasing order, states are the generator indices.
import sys, os
C='../bmw-census-left-orders-2026-09-17'; sys.path.insert(0,C); sys.path.insert(0,'.')
from lo_census import load
from selfrep import build
from aut import AUT
for idx in (332,193):
    G=next(G for i,G in load(os.path.join(C,'census_40_40.json')) if i==idx)
    for side in 'VH':
        K=build(G,side); X=K['X']; ix={l:i for i,l in enumerate(X)}
        out={a:tuple(ix[K['out'][(a,l)]] for l in X) for a in range(K['nL'])}
        sec={a:tuple(K['sec'][(a,l)] for l in X) for a in range(K['nL'])}
        o,s=AUT['%d%s'%(idx,side)]
        print(idx,side,'fixed letter f',K['f'],'X',X,'matches aut.py:',out==o and sec==s)
