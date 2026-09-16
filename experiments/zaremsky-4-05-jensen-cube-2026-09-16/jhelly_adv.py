"""Adversarial search for Helly failures of l^1-balls in finite convex
subcomplexes of RAAG Salvetti covers.

For centres z_0..z_{m-1} and offsets rho,
  gap(rho) = s_X(all) - max over (m-1)-subsets T of s_X(T),
where s_X(T) = min_{p in |K|} max_{i in T} (d(z_i,p) - rho_i).  gap > 0 means:
after adding gap to all radii... precisely, at radii rho + max_T s_X(T) every
m-1 balls meet and all m do not.  A minimal empty family of size m exists for
these centres iff gap > 0 for some rho.  Helly number k+1 says gap <= 0 for
m >= k+2.  Runs with m <= k+1 are the teeth check (positive gaps should occur).

rho is initialised critically (each (m-1)-subfamily is given a random witness
point in |K| and rho_i is the largest distance from z_i to its witnesses) and
then hill-climbed.
Usage: python3 jhelly_adv.py seed R configs steps graphs [m-offsets, e.g. 1,2,3]
"""
import sys, random, itertools
import numpy as np
from raagcube import RAAG, ball, hull_fast, Complex
from jhelly import GRAPHS, aff, s_X

GRAPHS = dict(GRAPHS)
GRAPHS["K3"] = (3, [(0, 1), (1, 2), (0, 2)])
GRAPHS["K2+K1"] = (3, [(0, 1)])
GRAPHS["K2*P4"] = (6, [(0, 1), (1, 2), (2, 3)] + [(a, b) for a in (4, 5) for b in range(4)] + [(4, 5)])


def gaps(K, cubes, Z, rho, js):
    rows = []
    for z, r in zip(Z, rho):
        a, const = aff(K, K.idx[z])
        rows.append((a, const, r))
    m = len(Z)
    cache = {}
    def sx(T):
        if T not in cache:
            cache[T] = s_X(K, cubes, [rows[i] for i in T])
        return cache[T]
    full = sx(tuple(range(m)))
    return {j: full - max(sx(T) for T in itertools.combinations(range(m), j)) for j in js}


def random_point(K, cubes, rng):
    f, m = rng.choice(cubes)
    c = np.array([float((f >> h) & 1) for h in range(K.nh)])
    for h in range(K.nh):
        if (m >> h) & 1:
            c[h] = rng.choice([0.0, 0.5, 1.0, rng.random()])
    return c


def critical_rho(K, cubes, Z, rng):
    m = len(Z)
    rho = [0.0] * m
    for T in itertools.combinations(range(m), m - 1):
        p = random_point(K, cubes, rng)
        for i in T:
            a, const = aff(K, K.idx[Z[i]])
            rho[i] = max(rho[i], float(a @ p + const))
    return rho


def climb(K, cubes, Z, steps, rng):
    m = len(Z)
    rho = critical_rho(K, cubes, Z, rng)
    best = gaps(K, cubes, Z, rho, [m - 1])[m - 1]
    for st in range(steps):
        i = rng.randrange(m)
        delta = rng.choice([0.5, 0.25, 0.125]) * rng.choice([-1, 1])
        new = list(rho); new[i] += delta
        g = gaps(K, cubes, Z, new, [m - 1])[m - 1]
        if g >= best - 1e-12:
            rho, best = new, g
    return best, rho


def run(name, R, configs, steps, rng, offsets):
    n, edges = GRAPHS[name]
    G = RAAG(n, edges)
    k = G.dim
    B = sorted(ball(G, R))
    for off in offsets:
        m = k + off
        worst = (-1e9, None)
        pos = 0
        for cf in range(configs):
            Z = rng.sample(B, m)
            K = Complex(G, hull_fast(G, Z))
            cubes = K.cubes()
            g, rho = climb(K, cubes, Z, steps, rng)
            if g > 1e-7:
                pos += 1
            if g > worst[0]:
                worst = (g, (Z, [round(r, 4) for r in rho], len(K.V)))
            if m >= k + 2 and g > 1e-7:
                print(name, "HELLY k+1 FAIL m=%d gap" % m, g, Z, rho)
        print(name, "k=%d m=%d configs=%d steps=%d positive=%d max gap=%.6f" % (k, m, configs, steps, pos, worst[0]))
        if worst[0] > 1e-7:
            print("   witness:", worst[1])
        sys.stdout.flush()


if __name__ == "__main__":
    seed = int(sys.argv[1]); R = int(sys.argv[2]); configs = int(sys.argv[3]); steps = int(sys.argv[4])
    names = sys.argv[5].split(",")
    offsets = [int(x) for x in sys.argv[6].split(",")] if len(sys.argv) > 6 else [1, 2, 3]
    rng = random.Random(seed)
    for nm in names:
        run(nm, R, configs, steps, rng, offsets)
