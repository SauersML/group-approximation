"""Exact deep_j(Q) versus law_j(Q) on STRUCTURED F(a,b)-sets Q:
right-regular (Cayley) actions of small 2-generated permutation groups,
and their coset actions G/H for small subgroups H.

Reuses foldlib/exact_search from experiments/fpbs-depth-overfolding-2026-09-17.
Strategy: compute law exactly (BFS over lawful seeds); then ask whether some
law-1 arbitrary same-fibre seeds already reach a partition containing ker(m).
Usage: python3 struct_search.py j maxorder [maxlaw]
"""
import os
import sys
import itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-depth-overfolding-2026-09-17'))
from foldlib import depth_graphs, closure, contains_kernel  # noqa: E402
from exact_search import canon, search  # noqa: E402


def compose(p, q):
    """(p then q) as right action: x -> q[p[x]]."""
    return tuple(q[x] for x in p)


def gen_group(al, be, cap):
    e = tuple(range(len(al)))
    els = [e]
    idx = {e: 0}
    i = 0
    while i < len(els):
        g = els[i]
        for s in (al, be):
            h = compose(g, s)
            if h not in idx:
                idx[h] = len(els)
                els.append(h)
                if len(els) > cap:
                    return None
        i += 1
    return els, idx


def cayley(al, be, cap):
    r = gen_group(al, be, cap)
    if r is None:
        return None
    els, idx = r
    PA = [idx[compose(g, al)] for g in els]
    PB = [idx[compose(g, be)] for g in els]
    return PA, PB


def seeds_of(G, m):
    fib = {}
    for v in range(G.V):
        fib.setdefault(G.over[v], []).append(v)
    allp, lawp = {}, {}
    for vs in fib.values():
        for x in range(len(vs)):
            for y in range(x + 1, len(vs)):
                u, v = vs[x], vs[y]
                c = canon(closure(G, [(u, v)]))
                if m[u] == m[v]:
                    lawp.setdefault(c, (u, v))
                allp.setdefault(c, (u, v))
    return list(allp.values()), list(lawp.values())


def examine(PA, PB, j, maxlaw):
    Gj, G, m = depth_graphs(PA, PB, j)
    kerok = lambda cls: contains_kernel(G, cls, m)
    if kerok(list(range(G.V))):
        return G.V, Gj.V, 0, 0, None
    allp, lawp = seeds_of(G, m)
    law, _ = search(G, m, lawp, kerok, maxlaw)
    if law is None or law == 1:
        return G.V, Gj.V, law, law, None
    deep, wit = search(G, m, allp, kerok, law - 1)
    if deep is None:
        return G.V, Gj.V, law, law, None
    return G.V, Gj.V, law, deep, wit


def perms(d):
    return list(itertools.permutations(range(d)))


def main():
    j = int(sys.argv[1])
    maxorder = int(sys.argv[2])
    maxlaw = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    seen = set()
    for d in (3, 4, 5):
        P = perms(d)
        for al in P:
            for be in P:
                r = cayley(al, be, maxorder)
                if r is None:
                    continue
                PA, PB = r
                key = (tuple(PA), tuple(PB))
                if key in seen:
                    continue
                seen.add(key)
                Vj1, Vj, law, deep, wit = examine(PA, PB, j, maxlaw)
                flag = 'FLAG deep<law' if (deep is not None and law is not None
                                           and deep < law) else ''
                if law is None or law >= 2 or flag:
                    print('d', d, 'order', len(PA), 'a', al, 'b', be,
                          'V', Vj1, '->', Vj, 'law', law, 'deep', deep, flag)
                    sys.stdout.flush()
    print('distinct Cayley actions examined', len(seen))


if __name__ == '__main__':
    main()
