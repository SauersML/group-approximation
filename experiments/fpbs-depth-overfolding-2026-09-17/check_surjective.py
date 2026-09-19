"""Check item 1: m : Gamma_{j+1}(Q) -> Gamma_j(Q) is onto on vertices and
edges, and Gamma_{j+1}/ker(m) has exactly the vertices of Gamma_j.
Also checks that ker(m) is fold-closed (closure of ker equals ker).
Usage: python3 check_surjective.py n jmax trials seed
"""
import random
import sys
from foldlib import random_q, depth_graphs, closure


def edges(G):
    out = set()
    for v in range(G.V):
        for k, u in G.nb[v].items():
            out.add((v, k, u))
    return out


def main():
    n, jmax, trials, seed = [int(x) for x in sys.argv[1:5]]
    rng = random.Random(seed)
    bad = 0
    for tr in range(trials):
        PA, PB = random_q(n, rng)
        for j in range(jmax + 1):
            Gj, G, m = depth_graphs(PA, PB, j)
            vok = set(m) == set(range(Gj.V))
            img = {(m[v], k, m[u]) for (v, k, u) in edges(G)}
            eok = img == edges(Gj)
            fib = {}
            for v in range(G.V):
                fib.setdefault(m[v], []).append(v)
            pairs = [(vs[0], x) for vs in fib.values() for x in vs[1:]]
            cls = closure(G, pairs)
            kok = all((cls[u] == cls[v]) == (m[u] == m[v])
                      for u in range(G.V) for v in range(G.V))
            if not (vok and eok and kok):
                bad += 1
            print('trial', tr, 'j', j, 'V', G.V, '->', Gj.V,
                  'onto-vertices', vok, 'onto-edges', eok,
                  'ker fold-closed', kok)
    print('failures', bad)


if __name__ == '__main__':
    main()
