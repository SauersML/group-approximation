#!/usr/bin/env python3
"""Minimal-window Shannon LP on Z/p for the shape of the Z/7 fake (E={0,1,2,5}, F=E):
|E| = K with 0 in E, F = E + c or F = -E + c.  Configurations are identified under the automorphisms
x -> a x (a a unit) and the re-centring (E, F) -> (E + b, F - b), which preserve the LP value.
Only configurations with ground set at most MAXN are solved.

usage: cyclic_prime_scan.py p MAXN [K]
"""
import sys, os, itertools, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'shannon-window-certificates-2026-09-17'))
from shannon_lp import build, solve, show
from random_scan import Cyc

p, maxn = int(sys.argv[1]), int(sys.argv[2])
K = int(sys.argv[3]) if len(sys.argv) > 3 else 4
G = Cyc(p)

def key(E, F):
    best = None
    for a in range(1, p):
        for b in range(p):
            k = (tuple(sorted((a * e + b) % p for e in E)), tuple(sorted((a * f - b) % p for f in F)))
            if best is None or k < best:
                best = k
    return best

seen = set()
cnt = low = 0
for rest in itertools.combinations(range(1, p), K - 1):
    E = [0] + list(rest)
    for sgn in (1, -1):
        for c in range(p):
            F = sorted((sgn * e + c) % p for e in E)
            k = key(E, F)
            if k in seen:
                continue
            seen.add(k)
            d = build(G, E, F)
            if d['n'] > maxn:
                print('Z/%d E=%s F=%s n=%d skipped' % (p, show(G, E), show(G, F), d['n']), flush=True)
                continue
            t0 = time.time()
            res, _ = solve(d)
            cnt += 1
            flag = '  <<< BELOW 1' if res.fun < 1 - 1e-6 else ''
            low += bool(flag)
            print('Z/%d E=%s F=%s n=%d nv=%d LP=%.6f time=%.0fs%s' % (p, show(G, E), show(G, F), d['n'], d['nv'], res.fun, time.time() - t0, flag), flush=True)
print('# total %d configurations, %d below 1' % (cnt, low))
