#!/usr/bin/env python3
"""Exhaustive minimal-window Shannon LP scan of structured windows in torsion-free groups.

usage: box_scan.py GROUP KE KF MAXN [NPROC]
  GROUP in z2 (E, F in the box [-1,1]^2, both containing 0, deduplicated by
  translation (E+g, F-g) and the 8 lattice symmetries), heis, free (E, F in the
  radius-1 ball, both containing 1).
  KE = |E|, KF = |F|; configurations with ground set n > MAXN are skipped.
Only configurations where x_1 has at least two readers (1 in fE for two f) are solved.
Prints one line per configuration; LP < 1 - 1e-6 is flagged FAKE.
"""
import sys, os, itertools
from multiprocessing import Pool
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', 'shannon-window-certificates-2026-09-17'))
from shannon_lp import Free, Zd, build, solve, show

class Heis:
    one = (0, 0, 0)
    def mul(self, u, v):
        return (u[0] + v[0], u[1] + v[1], u[2] + v[2] + u[0] * v[1])
    def inv(self, u):
        return (-u[0], -u[1], -u[2] + u[0] * u[1])
    def show(self, u): return str(u)

SYM = [lambda p: p, lambda p: (-p[1], p[0]), lambda p: (-p[0], -p[1]), lambda p: (p[1], -p[0]),
       lambda p: (p[1], p[0]), lambda p: (-p[0], p[1]), lambda p: (p[0], -p[1]), lambda p: (-p[1], -p[0])]

def z2_key(E, F):
    best = None
    for s in SYM:
        E1 = [s(e) for e in E]; F1 = [s(f) for f in F]
        for e0 in E1:
            for f0 in F1:
                if (e0[0] + f0[0], e0[1] + f0[1]) != (0, 0):
                    continue
                k = (tuple(sorted((e[0] - e0[0], e[1] - e0[1]) for e in E1)),
                     tuple(sorted((f[0] + e0[0], f[1] + e0[1]) for f in F1)))
                if best is None or k < best:
                    best = k
    return best

def readers(G, E, F):
    return sum(1 for f in F if any(G.mul(f, e) == G.one for e in E))

def configs(name, KE, KF):
    if name == 'z2':
        G = Zd(2)
        box = [(i, j) for i in (-1, 0, 1) for j in (-1, 0, 1) if (i, j) != (0, 0)]
        seen = set()
        for Er in itertools.combinations(box, KE - 1):
            for Fr in itertools.combinations(box, KF - 1):
                E = [(0, 0)] + list(Er); F = [(0, 0)] + list(Fr)
                k = z2_key(E, F)
                if k in seen:
                    continue
                seen.add(k)
                yield G, list(k[0]), list(k[1])
    else:
        if name == 'heis':
            G = Heis()
            ball = [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]
        else:
            G = Free
            ball = ['a', 'A', 'b', 'B', 'c', 'C']
        for Er in itertools.combinations(ball, KE - 1):
            for Fr in itertools.combinations(ball, KF - 1):
                yield G, [G.one] + list(Er), [G.one] + list(Fr)

def run(arg):
    G, E, F, maxn = arg
    X = set([G.one] + [G.mul(f, e) for f in F for e in E])
    n = len(X) + len(F)
    if n > maxn or readers(G, E, F) < 2:
        return None
    # put a reader of x_1 first so that h(y_F0) is a reader's entropy (any f works by (T))
    d = build(G, E, F)
    res, _ = solve(d)
    val = res.fun if res.status == 0 else float('nan')
    tag = 'FAKE' if val < 1 - 1e-6 else 'ok'
    return '%s n=%d nv=%d E=%s F=%s LP=%.6f status=%d' % (tag, n, d['nv'], show(G, E), show(G, F), val, res.status)

if __name__ == '__main__':
    name, KE, KF, maxn = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    nproc = int(sys.argv[5]) if len(sys.argv) > 5 else 4
    jobs = [(G, E, F, maxn) for G, E, F in configs(name, KE, KF)]
    with Pool(nproc) as p:
        for line in p.imap_unordered(run, jobs):
            if line:
                print(line, flush=True)
