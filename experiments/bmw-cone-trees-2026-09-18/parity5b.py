# Independent recheck of parity5.py from the census squares alone (no lo_census / localact code).
# In Gamma, a square h v = v' h' read backwards says v' h' = h v, so the v-letter u = v' maps the
# neighbour h' o_H of the base vertex of the h-tree to h o_H (v fixes o_H).  This gives the permutation
# pi_u : h' -> h of the m = 5 h-letters.  A tree-compatible PGL_2(F) model with residue field F_4 forces
# every pi_u into PGL_2(F_4) = A_5, i.e. even.  For each remaining (5,3) class we record the cycle type
# of every pi_u, and the first odd letter if there is one.
import json
from sympy.combinatorics import Permutation
C = '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17/'
REM = json.load(open('remaining.json')); old = json.load(open('parity5.json'))
out = {}; agree = 0
for pat in sorted(p for p in REM if p.startswith('5')):
    D = json.load(open(C + 'census_%s.json' % pat)); m, n = D['m'], D['n']; assert m == 5
    for ci in REM[pat]:
        SQ = [(tuple(x), tuple(y)) for x, y in D['reps'][ci]]
        pis = []
        for u in range(n):
            img = {}
            for (h, v), (v2, h2) in SQ:
                if v2 == u: assert h2 not in img; img[h2] = h
            assert sorted(img) == list(range(m)) and sorted(img.values()) == list(range(m))
            pis.append(Permutation([img[x] for x in range(m)]))
        odd = [u for u, p in enumerate(pis) if p.is_odd]
        key = '%s#%d' % (pat, ci)
        out[key] = dict(even=not odd, odd_letter=odd[0] if odd else None,
                        cycles=[sorted(len(c) for c in p.full_cyclic_form) for p in pis])
        agree += out[key]['even'] == old[key]['even']
print(len(out), 'classes;', sum(not v['even'] for v in out.values()), 'with an odd v-letter;',
      'agreement with parity5.json:', agree)
json.dump(out, open('parity5b.json', 'w'), indent=0)
