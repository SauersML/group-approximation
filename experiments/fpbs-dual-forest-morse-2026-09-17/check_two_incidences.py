#!/usr/bin/env python3
"""Brute-force sanity check for Lemmas 2-4 of
research/artifacts/fpbs/docs/dual-forest-morse-matching-one-relator.md.

It uses faithful models of two groups in the class, with m = 1:
  * BS(1,2) = <a,t | t a t^-1 a^-2>, letter s = t used twice (eps = -1),
    realised as affine maps x -> 2^k x + b with b in Z[1/2];
  * Z^2 = <a,b | a b a^-1 b^-1>, letter s = a (eps = -1).
Torsion cases (m >= 2) are not tested: no faithful finite model is used here.

For every cycle based in a ball it enumerates the s-edges its loop crosses. It
then checks the following:
  (L2) the loop visits |W| distinct vertices;
  (L3) every s-edge near the origin has exactly two incidences, in distinct
       cycles, with occurrence indices 1 and 2;
  (L4) the dual component of the base cycle grows without bound inside
       increasing balls.
Exit code 0 on success.
"""
from fractions import Fraction
import sys


def bs_mul(g, h):
    # g = (k, b) is x -> 2^k x + b; composition g*h (apply h first, then g) as right multiplication path
    k1, b1 = g
    k2, b2 = h
    return (k1 + k2, b1 + Fraction(2) ** k1 * b2)


BS = {
    'name': 'BS(1,2)',
    'gens': {'a': (0, Fraction(1)), 't': (1, Fraction(0))},
    'inv': lambda g: (-g[0], -g[1] / Fraction(2) ** g[0]),
    'mul': bs_mul,
    'e': (0, Fraction(0)),
    'w': ['t', 'a', 'T', 'A', 'A'],  # t a t^-1 a^-2, capital = inverse
    's': 't',
}


def z2_mul(g, h):
    return (g[0] + h[0], g[1] + h[1])


Z2 = {
    'name': 'Z^2',
    'gens': {'a': (1, 0), 'b': (0, 1)},
    'inv': lambda g: (-g[0], -g[1]),
    'mul': z2_mul,
    'e': (0, 0),
    'w': ['a', 'b', 'A', 'B'],
    's': 'a',
}


def letter(G, c):
    if c.islower():
        return G['gens'][c]
    return G['inv'](G['gens'][c.lower()])


def ball(G, r):
    out = {G['e']}
    frontier = {G['e']}
    for _ in range(r):
        new = set()
        for g in frontier:
            for c in list(G['gens']) + [x.upper() for x in G['gens']]:
                h = G['mul'](g, letter(G, c))
                if h not in out:
                    new.add(h)
        out |= new
        frontier = new
    return out


def loop(G, g):
    verts = [g]
    for c in G['w']:
        verts.append(G['mul'](verts[-1], letter(G, c)))
    return verts


def check(G, r_base=6, r_edge=2):
    w = G['w']
    s = G['s']
    assert G['mul'](G['e'], G['e']) == G['e']
    base = ball(G, r_base)
    incid = {}
    for g in base:
        v = loop(G, g)
        assert v[-1] == g, 'relator not trivial'
        if len(set(v[:-1])) != len(w):
            print('L2 fails at', g)
            return False
        occ = 0
        for p, c in enumerate(w):
            if c.lower() != s:
                continue
            occ += 1
            lo = v[p] if c.islower() else v[p + 1]
            incid.setdefault(lo, []).append((g, occ))
    for lo in ball(G, r_edge):
        inc = incid.get(lo, [])
        if len(inc) != 2 or inc[0][0] == inc[1][0] or sorted(o for _, o in inc) != [1, 2]:
            print('L3 fails at edge with lower endpoint', lo, inc)
            return False
    # dual graph restricted to the base ball (m = 1: cycles = base points)
    adj = {}
    for lo, inc in incid.items():
        if len(inc) == 2:
            (g1, _), (g2, _) = inc
            adj.setdefault(g1, set()).add(g2)
            adj.setdefault(g2, set()).add(g1)
    comp = {G['e']}
    stack = [G['e']]
    while stack:
        x = stack.pop()
        for y in adj.get(x, ()):
            if y not in comp:
                comp.add(y)
                stack.append(y)
    print(G['name'], 'L2 L3 ok; dual component of base cycle inside ball of radius',
          r_base, 'has', len(comp), 'cycles')
    return len(comp)


def main():
    ok = True
    for G in (Z2, BS):
        sizes = []
        for r in (4, 6, 8):
            res = check(G, r_base=r, r_edge=2)
            if res is False:
                ok = False
                break
            sizes.append(res)
        if ok and not (sizes[0] < sizes[1] < sizes[2]):
            print('L4 growth check fails', sizes)
            ok = False
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
