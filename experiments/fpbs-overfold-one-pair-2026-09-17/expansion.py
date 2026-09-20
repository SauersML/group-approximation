"""The phi-expansion dictionary Exp(Gamma_0) and pair transfer candidates.

Exp(G0): vertices ('o',z) for z in V(G0); ('1',z) for z incident to a b-edge;
('2',e) for each b-edge e=(s,r).  Edges: a-edges of G0 on the o-part;
('o',z)-b->('1',z); ('1',s)-a->('2',e) and ('1',r)-b->('2',e) for e=(s,r).
Lemma 2 of the artifact: Exp(Gamma_{X0}) is folded and has pi_1 = phi(X0).
"""
import random, sys
from folding import *


def expansion(n0, E0):
    idx = {}

    def V(k):
        if k not in idx:
            idx[k] = len(idx)
        return idx[k]
    for z in range(n0):
        V(('o', z))
    edges = []
    bedges = [(u, v) for (u, l, v) in E0 if l == 'b']
    for (u, l, v) in E0:
        if l == 'a':
            edges.append((V(('o', u)), 'a', V(('o', v))))
    binc = sorted({u for e in bedges for u in e})
    for z in binc:
        edges.append((V(('o', z)), 'b', V(('1', z))))
    for (s, r) in bedges:
        edges.append((V(('1', s)), 'a', V(('2', (s, r)))))
        edges.append((V(('1', r)), 'b', V(('2', (s, r)))))
    return len(idx), edges, idx


def collapses(n, E, pairs):
    m, F, _ = fold(n, E, pairs)
    return is_rose(m, F)


if __name__ == '__main__':
    seed, T = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    ok = 0
    for trial in range(T):
        X0 = [rand_word(rng.randint(1, 7), rng) for _ in range(rng.randint(2, 4))]
        n0, E0 = graph_of(X0)
        n, E, idx = expansion(n0, E0)
        m, F, _ = fold(n, E)
        assert m == n, 'expansion not folded'
        assert canon(n, E) == canon(*graph_of([phi(w) for w in X0])), X0
        ok += 1
    print('expansion dictionary verified on', ok, 'random X0')
