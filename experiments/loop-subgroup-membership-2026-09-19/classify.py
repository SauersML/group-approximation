#!/usr/bin/env python3
"""Run the linear descent certificate on every survivor of the w20 poly-star screen."""
import sys as _sys, os as _os
_HERE = _os.path.dirname(_os.path.abspath(__file__))
for _d in ('loop-graph-screen-2026-09-18', 'poly-star-obstruction-2026-09-19'):
    _sys.path.insert(0, _os.path.join(_HERE, '..', _d))
import sys, itertools
from collections import Counter
import poly_star_screen as P
from descent import certify
kinds = sys.argv[1:] or ["chain", "fan", "cycle", "scycle"]
for kind in kinds:
    tally, low = Counter(), []
    for ps, pt, pu in itertools.product(P.PERMWORDS, repeat=3):
        for A, C, E in itertools.product(P.DECOS, repeat=3):
            R = P.family(kind, ps, pt, pu, A, C, E)
            v = P.analyse(R)
            if v[0] != "survivor": continue
            p, dim, lam = certify(R)
            tally[(p, dim)] += 1
            if dim < 2: low.append((ps, pt, pu, A, C, E, dim, lam))
    print("== family", kind, "survivors", sum(tally.values()), "(p, dim Lam) tally", dict(tally))
    for x in low: print("   dim<2", x)
    sys.stdout.flush()
