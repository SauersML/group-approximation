#!/usr/bin/env python3
"""The three Z/6 patterns whose canonical host Tietze-reduces to a one-relator presentation that is not a
proper power (ONE-REL-TF in base_rate.txt). Each host is in fact free of rank 2:

  case 1  <e0, e2, f3 | e0^-1 e2 e0^-1 e2 e0^-1 f3^-1 e0^-1 e2 e0^-1 f3^-1>
          Nielsen moves x = e0^-1 e2, y = e0^-1 f3^-1 turn the relator into x^2 y x y, a relator in x, y only,
          so H = <e0> * <x, y | x^2 y x y>. With z = x y the relator is x z^2, so x = z^-2 and y = z^3,
          and <x, y | x^2 y x y> = <z> = Z. Hence H = F(a, z) with e0 = a, e2 = a z^-2, f3 = z^-3 a^-1.
  case 2  the same relator with e0 -> e5, e2 -> e1, f3 -> f4.
  case 3  <e0, e4, f5 | e4 e0^-1 e4 f5 e4 e0^-1 e4 f5 e4 e0^-1>
          with x = e4 e0^-1, v = e4 f5 the relator is x v x v x, cyclically x^2 v x v, so again x = z^-2, v = z^3
          and H = F(a, z) with e4 = a, e0 = z^2 a, f5 = a^-1 z^3.

The script substitutes these values for the surviving letters, rebuilds the eliminated letters from the
Tietze history, checks that the relator maps to 1 and that the incidence pattern is reproduced exactly, and
solves LP on the free host.
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'shannon-window-certificates-2026-09-17'))
from shannon_lp import build, solve
from random_scan import Cyc
from host_tietze import canonical_host, tietze, free_reduce, inv
from free_host_lp import FreeN, pattern

A, Z = (0, 1), (1, 1)
def w(*letters):
    out = []
    for g, s in letters:
        out.append((g, s))
    return tuple(free_reduce(out))
a, ai, z, zi = (0, 1), (0, -1), (1, 1), (1, -1)

CASES = [
    ([0, 1, 2], [0, 1, 3], {'e0': w(a), 'e2': w(a, zi, zi), 'f3': w(zi, zi, zi, ai)}),
    ([0, 1, 5], [1, 2, 4], {'e5': w(a), 'e1': w(a, zi, zi), 'f4': w(zi, zi, zi, ai)}),
    ([0, 3, 4], [3, 4, 5], {'e4': w(a), 'e0': w(z, z, a), 'f5': w(ai, z, z, z)}),
]


def main():
    G, FN = Cyc(6), FreeN()
    for E, F, alive_vals in CASES:
        names, image, rels = canonical_host(G, E, F)
        hist = []
        alive, red = tietze(len(names), rels, None, hist)
        assert sorted(names[g] for g in alive) == sorted(alive_vals), (names, alive)
        val = {g: alive_vals[names[g]] for g in alive}
        for rel in red:
            ww = []
            for h, s in rel:
                ww.extend(val[h] if s == 1 else inv(list(val[h])))
            assert not free_reduce(ww), 'relator does not vanish'
        for g, repl in reversed(hist):
            ww = []
            for h, s in repl:
                ww.extend(val[h] if s == 1 else inv(list(val[h])))
            val[g] = tuple(free_reduce(ww))
        nE = len(E)
        EH = [val[i] for i in range(nE)]
        FH = [val[nE + j] for j in range(len(F))]
        assert pattern(G, E, F) == pattern(FN, EH, FH)
        d = build(FN, EH, FH)
        res, _ = solve(d)
        print('ONEREL-FREE z6 E=%s F=%s host E=%s F=%s n=%d LP=%.6f' % (
            E, F, [FN.show(x) for x in EH], [FN.show(x) for x in FH], d['n'], res.fun), flush=True)


if __name__ == '__main__':
    main()
