#!/usr/bin/env python3
"""Soundness check of the descent certificate on the whole screen (not only survivors):
every certified functional must vanish on E(w) whenever a short word w has finite order
(w^o = 1 is a relator with E = o E(w)).  Words: letters, loops, and products of two letters."""
import sys as _sys, os as _os
_HERE = _os.path.dirname(_os.path.abspath(__file__))
for _d in ('loop-graph-screen-2026-09-18', 'poly-star-obstruction-2026-09-19'):
    _sys.path.insert(0, _os.path.join(_HERE, '..', _d))
import sys, itertools, random
import poly_star_screen as P
from descent import certify
from loopgraph import W, reduce
kinds = sys.argv[1:-1] or ["chain"]; step = int(sys.argv[-1]) if len(sys.argv) > 1 else 7
tested = viol = fin = 0; dims = {}
for kind in kinds:
    allm = [(a, b) for a in itertools.product(P.PERMWORDS, repeat=3) for b in itertools.product(P.DECOS, repeat=3)]
    for idx in range(0, len(allm), step):
        (ps, pt, pu), (A, C, E) = allm[idx]
        R = P.family(kind, ps, pt, pu, A, C, E)
        p, dim, lam = certify(R); S = sorted(R.states); tested += 1
        dims[dim] = dims.get(dim, 0) + 1
        if dim == 0: continue
        words = [((s, 1),) for s in S] + [reduce(((s, 1), (t, e))) for s in S for t in S for e in (1, -1) if s < t]
        words += [a + ((s, e),) + b for s, e, y, a, b in R.loop_states(p) if e == 1]
        for w in words:
            o = R.order(w, 60)
            if o is None: continue
            fin += 1
            Ev = [sum(e for l, e in w if l == s) for s in S]
            if any(sum(x * y for x, y in zip(l, Ev)) for l in lam):
                viol += 1; print("VIOLATION", kind, ps, pt, pu, A, C, E, w, o, lam)
print("members", tested, "dims", dims, "finite-order words", fin, "violations", viol)
