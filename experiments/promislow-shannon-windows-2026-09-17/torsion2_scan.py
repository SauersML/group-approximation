#!/usr/bin/env python3
"""Minimal-window Shannon LP census over hosts whose only torsion has order 2.

Every group with torsion contains Z/p (p an odd prime), Z/4, (Z/2)^2, D_inf or Z x Z/2, or is Z/2.
Z/3, Z/4, Z/5 already carry exact fakes; this scans the order-2 hosts.

usage: torsion2_scan.py GROUP SEED COUNT MAXN     GROUP in k2 (=(Z/2)^2), k3 (=(Z/2)^3), dinf, zz2
"""
import sys, os, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'shannon-window-certificates-2026-09-17'))
from shannon_lp import build, solve, show

class Z2k:
    def __init__(self, k): self.one = (0,) * k
    def mul(self, u, v): return tuple((p + q) % 2 for p, q in zip(u, v))
    def inv(self, u): return u
    def show(self, u): return ''.join(map(str, u))

class Dinf:
    one = (1, 0)
    def mul(self, u, v): return (u[0] * v[0], u[0] * v[1] + u[1])
    def inv(self, u): return (u[0], -u[0] * u[1])
    def show(self, u): return ('r' if u[0] < 0 else '') + str(u[1])

class ZxZ2:
    one = (0, 0)
    def mul(self, u, v): return (u[0] + v[0], (u[1] + v[1]) % 2)
    def inv(self, u): return (-u[0], u[1])
    def show(self, u): return str(u)

def ball(G, gens, r):
    B = {G.one}
    for _ in range(r):
        B |= {G.mul(b, s) for b in B for s in gens}
    return sorted(B, key=str)

def group(name):
    if name == 'k2':
        G = Z2k(2); gens = [(1, 0), (0, 1)]
    elif name == 'k3':
        G = Z2k(3); gens = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
    elif name == 'dinf':
        G = Dinf(); gens = [(-1, 0), (-1, 1)]
    elif name == 'zz2':
        G = ZxZ2(); gens = [(1, 0), (-1, 0), (0, 1)]
    return G, gens

if __name__ == '__main__':
    name, seed, count, maxn = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    G, gens = group(name)
    rng = random.Random(seed)
    B = ball(G, gens, 3)
    seen = set(); done = 0; tries = 0
    while done < count and tries < 20000:
        tries += 1
        kE = rng.choice([2, 3, 3, 4, 4])
        others = [b for b in B if b != G.one]
        E = [G.one] + rng.sample(others, min(kE - 1, len(others)))
        Einv = [G.inv(e) for e in E]
        nr = rng.choice([2, 2, 3, 4])
        R = rng.sample(Einv, min(nr, len(Einv)))
        nonr = [b for b in B if b not in Einv]
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
        print('%s E=%s F=%s n=%d nv=%d LP=%.6f%s' % (name, show(G, E), show(G, F), d['n'], d['nv'], res.fun, flag), flush=True)
