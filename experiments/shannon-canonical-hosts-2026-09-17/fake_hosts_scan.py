#!/usr/bin/env python3
"""Scan finite and order-2 hosts for minimal-window Shannon fakes and classify each fake's canonical host.

usage: fake_hosts_scan.py GROUP MAXE MAXF MAXN
GROUP in z3..z8, k2, s3, z2z4, dinf7 (the single D_inf fake), z7fake (the single Z/7 fake)
Exhaustive over E containing 1 with 2 <= |E| <= MAXE and F with 2 <= |F| <= MAXF meeting E^-1
(so 1 is read at least once), ground set size <= MAXN.
"""
import sys, os, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'shannon-window-certificates-2026-09-17'))
sys.path.insert(0, os.path.join(HERE, '..', 'promislow-shannon-windows-2026-09-17'))
from shannon_lp import build, solve, show
from random_scan import Cyc, Perm
from torsion2_scan import Z2k, Dinf
from host_tietze import classify, word_str


class Prod:
    def __init__(self, a, b):
        self.a, self.b = a, b; self.one = (a.one, b.one)
    def mul(self, u, v): return (self.a.mul(u[0], v[0]), self.b.mul(u[1], v[1]))
    def inv(self, u): return (self.a.inv(u[0]), self.b.inv(u[1]))
    def show(self, u): return '(%s,%s)' % (self.a.show(u[0]), self.b.show(u[1]))


def elements(G, gens):
    S = {G.one}; frontier = [G.one]
    while frontier:
        nxt = []
        for x in frontier:
            for s in gens:
                y = G.mul(x, s)
                if y not in S:
                    S.add(y); nxt.append(y)
        frontier = nxt
    return sorted(S, key=str)


def report(G, E, F, val):
    kind, names, alive, red, cert = classify(G, E, F)
    line = '  host=%s gens=%d rels=%s' % (kind, len(alive), [word_str(names, r) for r in red][:4])
    if cert:
        line += ' cert=(%s)^%d' % (word_str(names, cert[0]), cert[1])
    return kind, line


def main():
    name, maxE, maxF, maxn = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    configs = None
    if name.startswith('z') and name[1:].isdigit():
        n = int(name[1:]); G = Cyc(n); elems = list(range(n))
    elif name == 'k2':
        G = Z2k(2); elems = elements(G, [(1, 0), (0, 1)])
    elif name == 's3':
        G = Perm(3, None); elems = elements(G, [(1, 0, 2), (1, 2, 0)])
    elif name == 'z2z4':
        G = Prod(Cyc(2), Cyc(4)); elems = elements(G, [(1, 0), (0, 1)])
    elif name == 'dinf7':
        G = Dinf(); configs = [([(1, 0), (-1, 0), (-1, 1), (1, 1)], [(-1, 1), (1, -1), (1, 0), (1, 1)])]
    elif name == 'z7fake':
        G = Cyc(7); configs = [([0, 1, 2, 4], [0, 3, 5, 6])]
    if configs is None:
        configs = []
        others = [g for g in elems if g != G.one]
        for kE in range(2, maxE + 1):
            for Er in itertools.combinations(others, kE - 1):
                E = [G.one] + list(Er)
                Einv = {G.inv(e) for e in E}
                for kF in range(2, maxF + 1):
                    for F in itertools.combinations(elems, kF):
                        if Einv & set(F):
                            configs.append((E, list(F)))
    counts = {}
    nfake = 0
    for E, F in configs:
        d = build(G, E, F)
        if d['n'] > maxn:
            continue
        res, _ = solve(d)
        if res.fun < 1 - 1e-6:
            nfake += 1
            kind, line = report(G, E, F, res.fun)
            counts[kind] = counts.get(kind, 0) + 1
            print('%s E=%s F=%s n=%d LP=%.6f' % (name, show(G, E), show(G, F), d['n'], res.fun), flush=True)
            print(line, flush=True)
    print('SUMMARY %s: %d fakes; host classes %s' % (name, nfake, counts), flush=True)


if __name__ == '__main__':
    main()
