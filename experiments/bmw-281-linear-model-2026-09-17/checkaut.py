# Check that aut.AUT['281'] is the invariant-subtree automaton K of census_40_40 class #281, on both sides,
# as built by selfrep.build (experiments/bmw-census-left-orders-2026-09-17).  Run from this directory.
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'bmw-census-left-orders-2026-09-17'))
from lo_census import load
from selfrep import build
from aut import AUT
base = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'bmw-census-left-orders-2026-09-17', 'census_40_40.json')
out, sec = AUT['281']
for i, G in load(base):
    if i != 281: continue
    for side in 'VH':
        K = build(G, side)
        X = K['X']; rel = {l: j for j, l in enumerate(X)}   # letters != f, relabelled 0,1,2 in order
        ok = K['nL'] == 4 and all(rel[K['out'][(a, l)]] == out[a][rel[l]] and K['sec'][(a, l)] == sec[a][rel[l]]
                                  for a in range(4) for l in X)
        print('census_40_40 #281 side', side, 'fixed letter', K['f'], 'X', X, 'matches AUT[281]:', ok)
