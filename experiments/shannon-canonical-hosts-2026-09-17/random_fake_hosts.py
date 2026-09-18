#!/usr/bin/env python3
"""Random minimal-window configurations in larger finite groups; every fake gets its canonical host classified.

The aim is a fake whose incidence pattern does not force torsion. Such a fake with a torsion-free canonical
host would refute torsion-free-windows-have-minimal-shannon-certificates by the transfer lemma.

usage: random_fake_hosts.py GROUP SEED COUNT MAXN     GROUP in s4, z13, z3z3, heis3
"""
import sys, os, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'shannon-window-certificates-2026-09-17'))
sys.path.insert(0, os.path.join(HERE, '..', 'promislow-shannon-windows-2026-09-17'))
from shannon_lp import build, solve, show
from random_scan import Cyc, Perm
from fake_hosts_scan import Prod, elements, report


class Heis3:
    one = (0, 0, 0)
    def mul(self, u, v): return ((u[0] + v[0]) % 3, (u[1] + v[1]) % 3, (u[2] + v[2] + u[0] * v[1]) % 3)
    def inv(self, u): return ((-u[0]) % 3, (-u[1]) % 3, (-u[2] + u[0] * u[1]) % 3)
    def show(self, u): return ''.join(map(str, u))


def group(name):
    if name == 's4':
        G = Perm(4, None); return G, elements(G, [(1, 0, 2, 3), (1, 2, 3, 0)])
    if name == 'z13':
        G = Cyc(13); return G, list(range(13))
    if name == 'z3z3':
        G = Prod(Cyc(3), Cyc(3)); return G, elements(G, [(1, 0), (0, 1)])
    if name == 'heis3':
        G = Heis3(); return G, elements(G, [(1, 0, 0), (0, 1, 0)])


def main():
    name, seed, count, maxn = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    G, elems = group(name)
    rng = random.Random(seed)
    others = [g for g in elems if g != G.one]
    seen, done, tries, nfake, counts = set(), 0, 0, 0, {}
    while done < count and tries < 100000:
        tries += 1
        E = [G.one] + rng.sample(others, rng.choice([2, 3, 3]))
        # at least two readers of the special site
        readers = rng.sample([G.inv(e) for e in E], 2)
        F = list(dict.fromkeys(readers + rng.sample(elems, rng.choice([0, 1, 1, 2]))))
        key = (tuple(sorted(map(str, E))), tuple(sorted(map(str, F))))
        if key in seen:
            continue
        seen.add(key)
        d = build(G, E, F)
        if d['n'] > maxn:
            continue
        res, _ = solve(d)
        done += 1
        if res.fun < 1 - 1e-6:
            nfake += 1
            kind, line = report(G, E, F, res.fun)
            counts[kind] = counts.get(kind, 0) + 1
            print('%s E=%s F=%s n=%d LP=%.6f' % (name, show(G, E), show(G, F), d['n'], res.fun), flush=True)
            print(line, flush=True)
    print('SUMMARY %s seed %d: %d configurations, %d fakes; host classes %s' % (name, seed, done, nfake, counts), flush=True)


if __name__ == '__main__':
    main()
