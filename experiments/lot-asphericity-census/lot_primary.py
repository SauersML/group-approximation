#!/usr/bin/env python3
"""Primary-source certification pipeline for LOT complexes.

Only tests whose theorems were read in the primary papers:
  inj     Harlander--Rosebrock, Math. Z. 287 (2017), Thm 1.1
  IT      Barreto--Minian arXiv:2308.07447 Cor. 3.1, with H_2 = 0 (their introduction)
  itest   Barmak--Minian arXiv:1601.00604, Thms 2.6/2.8
  weight  Harlander--Rosebrock arXiv:1912.12512 Def. 3.5 (nonnegative weights)
  bm25/bm218 and label presentations: lot2.py
  relative: Harlander--Rosebrock arXiv:1912.12512 Thms 3.4 and 2.4 (lot3.py)
Reductions: Harlander--Rosebrock arXiv:1212.1943 Sec. 1 (3-deformations).
"""
import itertools
from lot import reduce_lot, test_inj, test_IT, test_itest, test_weight
from lot2 import certify2
from lot3 import sub_lots, rel_forest

PRIMARY = [('inj', test_inj), ('IT', test_IT), ('itest', test_itest), ('weight', test_weight)]

def certify_primary(n, E, depth=0):
    rn, rE = reduce_lot(n, E)
    if rn <= 1: return 'trivial', {}          # one generator, no relators: a circle
    for name, f in PRIMARY:
        c = f(rn, rE)
        if c is not None: return name, c
    name, c = certify2(rn, rE)
    if name: return name, c
    if depth < 3:
        c = relative_primary(rn, rE, depth)
        if c: return 'relative', c
    return None, None

def relative_primary(n, E, depth=0, max_family=3):
    subs, cache = sub_lots(n, E), {}
    def sub_ok(s):
        if s[0] not in cache:
            idx = {v: r for r, v in enumerate(sorted(s[1]))}
            cache[s[0]] = certify_primary(len(s[1]), [tuple(idx[x] for x in e) for e in s[2]], depth + 1)[0]
        return cache[s[0]]
    for size in range(1, max_family + 1):
        for fam in itertools.combinations(subs, size):
            Vs = [s[1] for s in fam]
            if any(a & b for a, b in itertools.combinations(Vs, 2)): continue
            Vall, Kmask = set().union(*Vs), 0
            for s in fam: Kmask |= s[0]
            if any(not (Kmask >> k & 1) and {i, l, t} <= Vall for k, (i, l, t) in enumerate(E)):
                continue
            for side in ('I', 'T'):
                if rel_forest(n, E, fam, Kmask, side) and all(sub_ok(s) for s in fam):
                    return {'side': side, 'subs': [s[2] for s in fam],
                            'sub_tests': [cache[s[0]] for s in fam]}
    return None
