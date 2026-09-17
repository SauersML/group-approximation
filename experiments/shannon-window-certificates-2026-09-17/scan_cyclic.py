#!/usr/bin/env python3
"""Exhaustive minimal-window Shannon LP over cyclic groups Z/n.

Every configuration whose sites all lie in a cyclic subgroup <t> of order n has the same
LP in any group G containing t (sites, translations p q^-1 and all products are computed in <t>).
So an LP value < 1 here gives a Shannon fake in every group with an element of order n.

usage: scan_cyclic.py n maxE maxF maxn
E ranges over subsets of Z/n containing 0 with 2 <= |E| <= maxE,
F over subsets meeting -E with |F| <= maxF, modulo the automorphisms u -> a u (a a unit)."""
import itertools, sys
from math import gcd
from random_scan import Cyc
from shannon_lp import build, solve, show

n, maxE, maxF, maxn = map(int, sys.argv[1:5])
G = Cyc(n)
units = [a for a in range(1, n) if gcd(a, n) == 1]
seen = set()
low = []
count = 0
for kE in range(2, maxE + 1):
    for Er in itertools.combinations(range(1, n), kE - 1):
        E = [0] + list(Er)
        for kF in range(1, maxF + 1):
            for F in itertools.combinations(range(n), kF):
                if not set(F) & {(-e) % n for e in E}:
                    continue
                key = min((tuple(sorted(a * e % n for e in E)), tuple(sorted(a * f % n for f in F))) for a in units)
                if key in seen:
                    continue
                seen.add(key)
                d = build(G, E, list(F))
                if d['n'] > maxn:
                    continue
                res, _ = solve(d)
                count += 1
                flag = '  <<< BELOW 1' if res.fun < 1 - 1e-6 else ''
                if flag:
                    low.append((res.fun, E, F))
                print('Z/%d E=%s F=%s n=%d LP=%.6f%s' % (n, show(G, E), show(G, F), d['n'], res.fun, flag), flush=True)
print('SUMMARY Z/%d: %d configurations, %d below 1, min %s' % (n, count, len(low), min(low)[0] if low else None))
