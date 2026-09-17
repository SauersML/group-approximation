#!/usr/bin/env python3
"""Solve the minimal-window Shannon LP directly on FREE canonical hosts.

For every configuration (E, F) of the exhaustive enumeration whose canonical host H_P is free after Tietze
elimination, reconstruct the letters of H_P as reduced words in the surviving free generators, check that
these words realize exactly the same incidence pattern (coincidences and products equal to 1), and solve
LP_{H_P}. By Corollary 2 of the artifact, LP_{H_P} is the minimum of the LP over all realizations of the
pattern, so LP_{H_P} >= 1 means: no group at all realizes this pattern with a fake.

Together with base_rate.py (every other pattern forces torsion), this checks the strengthening
fake-incidence-patterns-force-torsion on every pattern of the enumeration.

usage: free_host_lp.py GROUP MAXE MAXF MAXN
"""
import sys, os, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'shannon-window-certificates-2026-09-17'))
sys.path.insert(0, os.path.join(HERE, '..', 'promislow-shannon-windows-2026-09-17'))
from shannon_lp import build, solve
from random_scan import Cyc, Perm
from torsion2_scan import Z2k
from host_tietze import canonical_host, tietze, free_reduce, inv
from fake_hosts_scan import elements


class FreeN:
    """Free group on integer generators; elements are reduced tuples of (gen, sign)."""
    one = ()
    def mul(self, u, v): return tuple(free_reduce(list(u) + list(v)))
    def inv(self, u): return tuple(inv(list(u)))
    def show(self, u): return '.'.join('%d%s' % (g, '' if s == 1 else "'") for g, s in u) or '1'


def free_realization(G, E, F):
    names, image, rels = canonical_host(G, E, F)
    hist = []
    alive, red = tietze(len(names), rels, None, hist)
    if red:
        return None
    val = {g: ((g, 1),) for g in alive}
    for g, repl in reversed(hist):
        w = []
        for h, s in repl:
            w.extend(val[h] if s == 1 else inv(list(val[h])))
        val[g] = tuple(free_reduce(w))
    nE = len(dict.fromkeys(E))
    return [val[i] for i in range(nE)], [val[nE + j] for j in range(len(names) - nE)]


def pattern(G, E, F):
    prods = {}
    for j, f in enumerate(F):
        for i, e in enumerate(E):
            prods.setdefault(G.mul(f, e), []).append((j, i))
    return sorted(sorted(v) for v in prods.values()), sorted(tuple(v) for k, v in prods.items() if k == G.one)


def main():
    name, maxE, maxF, maxn = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    if name.startswith('z') and name[1:].isdigit():
        n = int(name[1:]); G = Cyc(n); elems = list(range(n))
    elif name == 'k2':
        G = Z2k(2); elems = elements(G, [(1, 0), (0, 1)])
    elif name == 's3':
        G = Perm(3, None); elems = elements(G, [(1, 0, 2), (1, 2, 0)])
    others = [g for g in elems if g != G.one]
    FN = FreeN()
    nfree, minval, worst, below = 0, 9.0, None, 0
    for kE in range(2, maxE + 1):
        for Er in itertools.combinations(others, kE - 1):
            E = [G.one] + list(Er)
            Einv = {G.inv(e) for e in E}
            for kF in range(2, maxF + 1):
                for F in itertools.combinations(elems, kF):
                    F = list(F)
                    if not (Einv & set(F)):
                        continue
                    if build(G, E, F)['n'] > maxn:
                        continue
                    r = free_realization(G, E, F)
                    if r is None:
                        continue
                    EH, FH = r
                    assert pattern(G, E, F) == pattern(FN, EH, FH), (E, F, EH, FH)
                    d = build(FN, EH, FH)
                    res, _ = solve(d)
                    nfree += 1
                    if res.fun < minval:
                        minval, worst = res.fun, (E, F, [FN.show(x) for x in EH], [FN.show(x) for x in FH], d['n'])
                    if res.fun < 1 - 1e-6:
                        below += 1
                        print('FAKE ON FREE HOST %s E=%s F=%s host E=%s F=%s LP=%.6f' % (
                            name, E, F, [FN.show(x) for x in EH], [FN.show(x) for x in FH], res.fun), flush=True)
    print('FREEHOST %s: %d free-host patterns solved on the free host; fakes %d; min LP %.6f at %s' % (
        name, nfree, below, minval, worst), flush=True)


if __name__ == '__main__':
    main()
