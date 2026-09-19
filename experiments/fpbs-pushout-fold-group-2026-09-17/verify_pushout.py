#!/usr/bin/env python3
"""Independent check of  N/<<K cap N>>^N  =  P_V  by counting homomorphisms.

Hom(N/<<K cap N>>, S) is computed directly from the Schreier graph: a hom N -> S
is an S-connection on the {b,c}-Schreier graph, trivial on a spanning tree; it
kills K cap N iff its holonomy is trivial on every closed loop of the
K-Schreier graph (generators c and a = b^-1 c b^2, the a-edge from v being the
path b^-1 c b b).  Compared with the coloring count of P_V from foldgroup.py.
"""
import itertools, random, sys
sys.path.insert(0, '.')
from foldgroup import *

def direct_count(Pb, Pc, mul, inv, one):
    n = len(Pb); Pbi = pinv(Pb)
    edges = [('b', v) for v in range(n)] + [('c', v) for v in range(n)]
    tgt = lambda e: Pb[e[1]] if e[0] == 'b' else Pc[e[1]]
    # BFS spanning tree of the undirected Schreier graph
    tree, seen, st = set(), {0}, [0]
    while st:
        v = st.pop()
        for e in edges:
            u, w = e[1], tgt(e)
            for (x, y) in ((u, w), (w, u)):
                if x == v and y not in seen:
                    seen.add(y); tree.add(e); st.append(y)
    free = [e for e in edges if e not in tree]
    assert len(free) == n + 1
    total = 0
    for vals in itertools.product(range(len(mul)), repeat=n + 1):
        phi = {e: one for e in tree}
        phi.update(dict(zip(free, vals)))
        def a_edge(v):  # holonomy of path b^-1 c b b from v, and endpoint
            w = Pbi[v]; h = inv[phi[('b', w)]]
            h = mul[h][phi[('c', w)]]; w = Pc[w]
            h = mul[h][phi[('b', w)]]; w = Pb[w]
            h = mul[h][phi[('b', w)]]; w = Pb[w]
            return h, w
        g = {0: one}; st = [0]; ok = True
        while st and ok:
            v = st.pop()
            outs = [(phi[('c', v)], Pc[v]), a_edge(v)]
            for (h, w) in outs:
                want = mul[g[v]][h]
                if w in g:
                    if g[w] != want:
                        ok = False; break
                else:
                    g[w] = want; st.append(w)
        if ok and len(g) == n:
            # also check incoming K-edges consistency (all edges covered as outs)
            total += 1
    return total

if __name__ == "__main__":
    rng = random.Random(3)
    G = small_groups(); bad = 0; done = 0
    for trial in range(40):
        n = rng.choice([2, 3, 4])
        Pb, Pc = random_lset(n, rng); tr = triples(Pb, Pc)
        for k in ['C2', 'C3', 'S3']:
            mul, inv, one = table(G[k])
            d = direct_count(Pb, Pc, mul, inv, one)
            c = count_colorings(tr, n, mul, inv)
            done += 1
            if d != c:
                bad += 1; print('MISMATCH', n, k, d, c, Pb, Pc)
    print('checked', done, 'mismatches', bad)
