#!/usr/bin/env python3
"""Minimal-window Shannon LP census over the Hantzsche-Wendt (Promislow) group.

The group is torsion-free, virtually Z^3, not left-orderable and without unique products.
It is realised by affine maps of Z^3 (doubled coordinates):
    a: (X,Y,Z) -> ( X+1, -Y+1, -Z  )
    b: (X,Y,Z) -> (-X  ,  Y+1, -Z+1)
An element is (s, t) with s a sign vector (diagonal linear part) and t in Z^3; (s,t)(p) = s*p + t.

usage: hw_scan.py MODE SEED COUNT MAXN [RADIUS]
MODE = hw (random configurations with >= 2 readers of the special site, as random_scan.py)
     | klein (Klein bottle group, for comparison)
"""
import sys, os, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'shannon-window-certificates-2026-09-17'))
from shannon_lp import build, solve, show

class HW:
    one = ((1, 1, 1), (0, 0, 0))
    def mul(self, u, v):  # (uv)(p) = u(v(p))
        su, tu = u; sv, tv = v
        return (tuple(p * q for p, q in zip(su, sv)), tuple(p * q + r for p, q, r in zip(su, tv, tu)))
    def inv(self, u):  # p = s q + t  ->  q = s p - s t
        s, t = u
        return (s, tuple(-p * q for p, q in zip(s, t)))
    def show(self, u):
        s, t = u
        return '[' + ''.join('+' if x > 0 else '-' for x in s) + ' %d,%d,%d]' % t

A = ((1, -1, -1), (1, 1, 0))
B = ((-1, 1, -1), (0, 1, 1))

def gens_hw(G):
    return [A, G.inv(A), B, G.inv(B)]

class Klein:
    one = (0, 0)
    def mul(self, u, v): return (u[0] + (-1) ** (u[1] % 2) * v[0], u[1] + v[1])
    def inv(self, u): return (-(-1) ** (u[1] % 2) * u[0], -u[1])
    def show(self, u): return str(u)

def ball(G, gens, r):
    Bl = {G.one}
    for _ in range(r):
        Bl |= {G.mul(b, s) for b in Bl for s in gens}
    return sorted(Bl, key=str)

def selftest(G):
    one = G.one
    # torsion-free on a ball: no element of order 2..8 besides 1
    Bl = ball(G, gens_hw(G), 3)
    for g in Bl:
        p = g
        for k in range(2, 9):
            p = G.mul(p, g)
            assert p != one or g == one, 'torsion %s' % G.show(g)
    # Promislow relations: a^-1 b^2 a = b^-2, b^-1 a^2 b = a^-2
    a, b, ai, bi = A, B, G.inv(A), G.inv(B)
    b2 = G.mul(b, b); a2 = G.mul(a, a)
    assert G.mul(G.mul(ai, b2), a) == G.inv(b2)
    assert G.mul(G.mul(bi, a2), b) == G.inv(a2)
    return len(Bl)

if __name__ == '__main__':
    mode, seed, count, maxn = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    radius = int(sys.argv[5]) if len(sys.argv) > 5 else 2
    if mode == 'hw':
        G = HW(); gens = gens_hw(G); print('# selftest ball3 size', selftest(G), flush=True)
    else:
        G = Klein(); gens = [(1, 0), (-1, 0), (0, 1), (0, -1)]
    rng = random.Random(seed)
    Bl = ball(G, gens, radius)
    seen = set(); done = 0; tries = 0
    while done < count and tries < 200000:
        tries += 1
        kE = rng.choice([3, 3, 4])
        others = [b for b in Bl if b != G.one]
        E = [G.one] + rng.sample(others, kE - 1)
        Einv = [G.inv(e) for e in E]
        nr = rng.choice([2, 2, 3])
        R = rng.sample(Einv, min(nr, len(Einv)))
        nonr = [b for b in Bl if b not in Einv]
        nn = rng.choice([0, 1, 1, 2])
        N = rng.sample(nonr, min(nn, len(nonr)))
        F = R + N
        key = (tuple(sorted(map(str, E))), tuple(sorted(map(str, F))))
        if key in seen:
            continue
        seen.add(key)
        d = build(G, E, F)
        if d['n'] > maxn:
            continue
        res, _ = solve(d)
        done += 1
        flag = '  <<< BELOW 1' if res.fun < 1 - 1e-6 else ''
        print('%s E=%s F=%s n=%d nv=%d LP=%.6f%s' % (mode, show(G, E), show(G, F), d['n'], d['nv'], res.fun, flag), flush=True)
