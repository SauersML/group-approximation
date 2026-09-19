"""Pair automaton of the depth-j problem.

core_j = Stallings graph of L_j = <a, t_j> (fold over the one-point set).
psi: core_{j+1} -> core_j is the immersion induced by L_{j+1} <= L_j.
Gamma_j(Q) = core_j x Sch(Q) (full fibre product), so a merge of two
vertices of Gamma_{j+1}(Q) over one point y is an unordered pair {x, x'}
of core_{j+1} at y.  Fold closure propagates a pair along every letter
that both x and x' carry (the pair graph D), and adds pairs by
transitivity inside a fibre.  A pair is lawful when psi(x) = psi(x').

Prints, for each j: core sizes, psi-fibre sizes, and the components of D
(split into lawful and overfold components) with their size, number of
independent cycles (edges - vertices + 1), and letters.
Usage: python3 pair_automaton.py jmax
"""
import sys
from foldlib import gamma, Graph, A, t, depth_graphs


def core(j):
    G = Graph(gamma([0], [0], [A, t(j)]), 1, [0], [0])
    return G


def pair_graph(C):
    V = C.V
    states = [(x, y) for x in range(V) for y in range(x + 1, V)]
    idx = {s: i for i, s in enumerate(states)}
    edges = set()
    for (x, y) in states:
        for k in C.nb[x]:
            if k in C.nb[y] and k[1] == 1:
                u, v = C.nb[x][k], C.nb[y][k]
                if u != v:
                    s2 = (min(u, v), max(u, v))
                    edges.add((idx[(x, y)], k[0], idx[s2]))
    return states, idx, edges


def components(nv, edges):
    par = list(range(nv))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for (u, _, v) in edges:
        par[f(u)] = f(v)
    comp = {}
    for v in range(nv):
        comp.setdefault(f(v), []).append(v)
    ecount = {}
    for (u, _, v) in edges:
        ecount[f(u)] = ecount.get(f(u), 0) + 1
    return comp, ecount


def main(jmax):
    for j in range(0, jmax + 1):
        C1 = core(j + 1)
        C0 = core(j)
        # psi via one-point depth graphs
        _, _, m = depth_graphs([0], [0], j)
        fib = {}
        for v in range(C1.V):
            fib.setdefault(m[v], []).append(v)
        states, idx, edges = pair_graph(C1)
        comp, ec = components(len(states), edges)
        law = {i for i, (x, y) in enumerate(states) if m[x] == m[y]}
        print('j', j, 'core_{j+1}', C1.V, 'core_j', C0.V,
              'psi-fibre sizes', sorted(len(f) for f in fib.values()))
        stats = {'lawful': [], 'over': []}
        for r, vs in comp.items():
            kind = 'lawful' if vs[0] in law else 'over'
            assert all((v in law) == (kind == 'lawful') for v in vs)
            cyc = ec.get(r, 0) - len(vs) + 1
            stats[kind].append((len(vs), cyc))
        for kind in stats:
            L = sorted(stats[kind])
            print('  ', kind, 'components', len(L), 'total pairs',
                  sum(s for s, _ in L), 'max size', max(s for s, _ in L) if L else 0,
                  'with cycles', sum(1 for _, c in L if c > 0),
                  'sizes', L if len(L) < 30 else L[-10:])


if __name__ == '__main__':
    main(int(sys.argv[1]))
