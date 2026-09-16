#!/usr/bin/env python3
"""Exact check of Proposition U and of the rotation-fixed-point lemma of Proposition S in
research/artifacts/zp-braid-cat0-pivot-obstructions-2026-09-16.md.

Usage: python3 prop_u_check.py [NMAX]      (default NMAX = 14)

For even n <= NMAX, P = {12, 34, ..., (n-1)n}, rho P = {23, ..., n1}, every universal vertex v (one block, a cyclic
interval I of length l, 2 <= l <= n-1):
  k(P, v) = |I| - #(blocks of P meeting I), the same for rho P;
  numerator of cos d_B(P, v) + cos d_B(v, rho P) (common positive denominator) = k(P,v) + k(rhoP,v) - 2ab/m,
  a = n/2, b = l - 1, m = n - 1.  Prop U: it equals -(l-1)/(n-1) < 0.  Checked with Fractions.
Also prints the closed form arccos(1/sqrt n) + arccos(-sqrt n/(n-2)) at v = {12} (in units of pi), and, for n <= 10,
checks by brute force that the only rotation-invariant noncrossing partitions are 0 and 1.
"""
import sys, math
from fractions import Fraction

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 14

def blocks_meeting(pairs, I):
    return sum(1 for b in pairs if b & I)

for n in range(4, NMAX + 1, 2):
    m = n - 1; a = n // 2
    P = [frozenset({2 * t, 2 * t + 1}) for t in range(a)]
    Q = [frozenset({(i + 1) % n for i in b}) for b in P]
    ok = True
    for s in range(n):
        for l in range(2, n):
            I = frozenset((s + t) % n for t in range(l))
            b = l - 1
            k1 = l - blocks_meeting(P, I); k2 = l - blocks_meeting(Q, I)
            num = Fraction(k1 + k2) - Fraction(2 * a * b, m)
            if num != Fraction(-(l - 1), n - 1):
                ok = False
    close = (math.acos(1 / math.sqrt(n)) + math.acos(-math.sqrt(n) / (n - 2))) / math.pi
    print("n = %2d | numerator == -(l-1)/(n-1) for all %d universal vertices: %s | at v={12}: %.6f pi" % (
        n, n * (n - 2), ok, close))

def set_partitions(n):
    def rec(i, blocks):
        if i == n:
            yield blocks; return
        for k in range(len(blocks)):
            nb = list(blocks); nb[k] = nb[k] | {i}
            yield from rec(i + 1, nb)
        yield from rec(i + 1, blocks + [{i}])
    yield from rec(0, [])

def crossing(b1, b2, n):
    for a in b1:
        for c in b1:
            if a < c:
                inside = {t for t in b2 if a < t < c}
                if inside and (b2 - inside):
                    return True
    return False

for n in range(3, min(NMAX, 10) + 1):
    inv = []
    for bl in set_partitions(n):
        if any(crossing(bl[i], bl[j], n) for i in range(len(bl)) for j in range(len(bl)) if i != j):
            continue
        canon = frozenset(frozenset(b) for b in bl)
        rot = frozenset(frozenset((i + 1) % n for i in b) for b in bl)
        if canon == rot:
            inv.append(len(bl))
    print("n = %2d | rotation-invariant noncrossing partitions have block counts %s (only 0 and 1 expected)" % (
        n, sorted(inv)))
