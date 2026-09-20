#!/usr/bin/env python3
"""Exact check that every class representative in classes(L) is a nontrivial element of F'.
PL maps over Q (trace_test.py). Nontrivial means the map moves some dyadic point. F' membership means
slope 1 at both ends, and the exponent sums vanish by construction.
Usage: python3 check_classes.py L"""

import sys
from fractions import Fraction as Q
from trace_test import word_pl, pick_order, ev, slope_germs
from constrained_census import classes

L = int(sys.argv[1]) if len(sys.argv) > 1 else 8
order = pick_order()
code = {"a": 0, "A": 1, "b": 2, "B": 3}
pts = [Q(k, 64) for k in range(1, 64)]
bad = 0
cls = classes(L)
for w in cls:
    f = word_pl([code[x] for x in w], order)
    moved = any(ev(f, p) != p for p in pts)
    s0, s1 = slope_germs(f)
    ok = moved and s0 == 1 and s1 == 1
    bad += not ok
    print(f"{w:10s} nontrivial={moved} end slopes=({s0},{s1})")
print(f"{len(cls)} classes, {bad} failures (composition order {order})")
