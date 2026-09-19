# Elementary obstruction on the valency-5 tree: the vertex stabiliser acts on the 5 neighbours through
# PGL_2(O_F) -> PGL_2(F_4) = A_5 (on P^1(F_4)), so every generator of the local action must be even.
# For each remaining (5,3) class: are all v-letter permutations of the 5 h-neighbours even?
import sys, json
sys.path.insert(0, '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17')
from lo_census import load
from localact import maps
from sympy.combinatorics import Permutation
C = '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17/'
REM = json.load(open('remaining.json')); LF = json.load(open('localfilter.json'))
res = {}
for pat in [p for p in REM if p.startswith('5')]:
    rem = set(REM[pat])
    for i, G in load(C + 'census_%s.json' % pat):
        if i not in rem: continue
        L, n, inv, step = maps(G, 'H'); assert n == 5
        gens = [Permutation([step(a, x)[0] for x in range(n)]) for a in range(L)]
        res['%s#%d' % (pat, i)] = dict(even=all(g.is_even for g in gens), order=LF['%s#%d' % (pat, i)]['H'])
from collections import Counter
print(len(res), Counter((v['even'], v['order']) for v in res.values()))
json.dump(res, open('parity5.json', 'w'), indent=0)
