#!/usr/bin/env python3
"""Random configurations with at least two readers of the special site, in several groups.
Prints every configuration with its Shannon LP value; flags LP < 1 - 1e-6.

usage: random_scan.py GROUP SEED COUNT MAXN
GROUP in free, z, z2, s3, z5, heis
"""
import random, sys, itertools
from shannon_lp import Free, Zd, build, solve, show

class Perm:
    def __init__(self, n, gens):
        self.one = tuple(range(n)); self.gens = gens
    def mul(self, u, v):  # (uv)(i) = u(v(i))
        return tuple(u[v[i]] for i in range(len(u)))
    def inv(self, u):
        r = [0] * len(u)
        for i, j in enumerate(u):
            r[j] = i
        return tuple(r)
    def show(self, u):
        return ''.join(map(str, u))

class Cyc:
    def __init__(self, n):
        self.n = n; self.one = 0
    def mul(self, u, v): return (u + v) % self.n
    def inv(self, u): return (-u) % self.n
    def show(self, u): return str(u)

class Heis:
    one = (0, 0, 0)
    def mul(self, u, v):
        return (u[0] + v[0], u[1] + v[1], u[2] + v[2] + u[0] * v[1])
    def inv(self, u):
        return (-u[0], -u[1], -u[2] + u[0] * u[1])
    def show(self, u): return str(u)

class BS12:
    """affine maps t -> 2^k t + m, stored as (k, m) with m a Fraction"""
    def __init__(self):
        from fractions import Fraction
        self.Fr = Fraction
        self.one = (0, Fraction(0))
    def mul(self, u, v):  # u(v(t)) = 2^ku (2^kv t + mv) + mu
        return (u[0] + v[0], u[1] + self.Fr(2) ** u[0] * v[1])
    def inv(self, u):
        return (-u[0], -u[1] / self.Fr(2) ** u[0])
    def show(self, u): return '(%d,%s)' % (u[0], u[1])

class Klein:
    one = (0, 0)
    def mul(self, u, v): return (u[0] + (-1) ** (u[1] % 2) * v[0], u[1] + v[1])
    def inv(self, u): return (-(-1) ** (u[1] % 2) * u[0], -u[1])
    def show(self, u): return str(u)

class ZxZn:
    def __init__(self, n):
        self.n = n; self.one = (0, 0)
    def mul(self, u, v): return (u[0] + v[0], (u[1] + v[1]) % self.n)
    def inv(self, u): return (-u[0], (-u[1]) % self.n)
    def show(self, u): return str(u)

def ball(G, gens, r):
    B = {G.one}
    for _ in range(r):
        B |= {G.mul(b, s) for b in B for s in gens}
    return sorted(B, key=str)

def group(name):
    if name == 'free':
        G = Free; gens = ['a', 'A', 'b', 'B']
    elif name == 'z':
        G = Zd(1); gens = [(1,), (-1,)]
    elif name == 'z2':
        G = Zd(2); gens = [(1, 0), (-1, 0), (0, 1), (0, -1)]
    elif name == 's3':
        G = Perm(3, None); gens = [(1, 0, 2), (0, 2, 1)]
    elif name == 'z5':
        G = Cyc(5); gens = [1, 4]
    elif name == 'heis':
        G = Heis(); gens = [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0)]
    elif name == 'bs12':
        G = BS12(); from fractions import Fraction as Fr
        gens = [(1, Fr(0)), (-1, Fr(0)), (0, Fr(1)), (0, Fr(-1))]
    elif name == 'klein':
        G = Klein(); gens = [(1, 0), (-1, 0), (0, 1), (0, -1)]
    elif name == 'zz3':
        G = ZxZn(3); gens = [(1, 0), (-1, 0), (0, 1), (0, 2)]
    elif name == 'z4':
        G = Cyc(4); gens = [1, 3]
    elif name == 'z7':
        G = Cyc(7); gens = [1, 6]
    return G, gens

if __name__ == '__main__':
    name, seed, count, maxn = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    G, gens = group(name)
    rng = random.Random(seed)
    B = ball(G, gens, 2)
    seen = set()
    done = 0
    tries = 0
    while done < count and tries < 100000:
        tries += 1
        kE = rng.choice([3, 3, 4])
        others = [b for b in B if b != G.one]
        if len(others) < kE - 1:
            continue
        E = [G.one] + rng.sample(others, kE - 1)
        Einv = [G.inv(e) for e in E]
        nr = rng.choice([2, 2, 3])
        R = rng.sample(Einv, min(nr, len(Einv)))
        BB = ball(G, gens, 2)
        nonr = [b for b in BB if b not in Einv]
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
