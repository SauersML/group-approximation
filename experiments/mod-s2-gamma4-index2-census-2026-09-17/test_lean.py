#!/usr/bin/env python3
"""Cross-check lean_eliminate against census.unit_eliminate on small coset
actions of H (levels given on the command line): same H_1 invariants, same
number of classes and class multiplicities, same W rank and augmentation gcd,
and same certificate l1."""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import index2 as I  # noqa: E402

C, G = I.C, I.G


def run(act, elim):
    ngen, rels, vs = G.rs(act)
    cols, Rr, V = elim(ngen, rels, vs)
    distinct = {}
    for v in V:
        k = tuple(sorted(v.items()))
        distinct[k] = distinct.get(k, 0) + 1
    keys = list(distinct)
    os.environ["INDEX2_SKIP_DISTANCE"] = "1"
    res = I.lattice(cols, Rr, [dict(k) for k in keys],
                    [distinct[k] for k in keys])
    return res, len(cols)


for N in [int(a) for a in sys.argv[1:]] or [2, 3]:
    objs, act = G.enumerate_Q(N)
    t = time.time()
    a, na = run(act, C.unit_eliminate)
    t1 = time.time()
    b, nb = run(act, I.lean_eliminate)
    t2 = time.time()
    print(N, len(act), "census:", a, na, f"{t1-t:.1f}s")
    print(N, len(act), "lean:  ", b, nb, f"{t2-t1:.1f}s")
    same = all(a[k] == b[k] for k in a)
    print("agree" if same else "DISAGREE")
    assert same
