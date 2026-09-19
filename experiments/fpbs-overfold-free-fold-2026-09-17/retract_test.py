"""Test of the retract route (G) on exact free-fold hits.

(G): for every hit J = <K, g_1..g_k> (J cap L_{j+1} = K, J cap L_j = K' of
index d), K' is a retract of J.  (G) implies rk(K':K) <= k (apply the
retraction to the generators), i.e. (O) on the component.
A necessary condition for K' to be a retract of J is that
H_1(K'; Z) -> H_1(J; Z) is split injective (Smith normal form of the
inclusion matrix is all ones).  This script runs the exact BFS of
bfs_free (all K classes of size d, realizable states only, depth kmax)
and, for every hit with J not inside L_j, records:
  (level, rk J - rk K', H_1 split injective?).
A hit where H_1 is not split kills the retract route (G).
Usage: python3 retract_test.py j d kmax [maxstates]
"""
import sys
from collections import Counter
from sympy import Matrix
from sympy.matrices.normalforms import smith_normal_form
from freefold import (core, cover, fold_with, cover_degree, transported_set,
                      law0)
from bfs_free import canon, relabel, classes

POS = [('a', 1), ('b', 1)]


def inside(nb, C):
    """True iff Gamma_J immerses into C (J <= L_C)."""
    lab = [None] * len(nb)
    lab[0] = 0
    st = [0]
    while st:
        v = st.pop()
        for k, u in nb[v].items():
            cu = C[lab[v]].get(k)
            if cu is None:
                return False
            if lab[u] is None:
                lab[u] = cu
                st.append(u)
            elif lab[u] != cu:
                return False
    return True


def tree_sigma(nb):
    """Spanning tree of nb.  Returns (sigma, disc) where sigma[(v,k)] is the
    generator index of the non-tree positive edge (v,k) and disc lists the
    tree edges (v, k, u) in discovery order (u discovered from v by k)."""
    par = {0: None}
    st = [0]
    tree = set()
    disc = []
    while st:
        v = st.pop()
        for k, u in nb[v].items():
            if u not in par:
                par[u] = v
                tree.add((v, k) if k[1] == 1 else (u, (k[0], 1)))
                disc.append((v, k, u))
                st.append(u)
    sigma = {}
    for v in range(len(nb)):
        for k in POS:
            if k in nb[v] and (v, k) not in tree:
                sigma[(v, k)] = len(sigma)
    return sigma, disc


def h1_split(nbJ, order, adj):
    """Is H_1(Gamma_{K'}) -> H_1(Gamma_J) split injective?  Gamma_{K'} is
    the pullback (order, adj); its vertex i lies over order[i][0]."""
    sigJ, _ = tree_sigma(nbJ)
    rJ = len(sigJ)

    def ev(v, k):
        """class in H_1(J) of traversing the pullback edge (v, k)."""
        vec = [0] * rJ
        if k[1] == 1:
            e = (order[v][0], k)
            s = 1
        else:
            e = (order[adj[v][k]][0], (k[0], 1))
            s = -1
        if e in sigJ:
            vec[sigJ[e]] = s
        return vec
    sigP, disc = tree_sigma(adj)
    phi = {0: [0] * rJ}
    for (v, k, u) in disc:
        w = ev(v, k)
        phi[u] = [phi[v][i] + w[i] for i in range(rJ)]
    cols = []
    for (v, k), _ in sorted(sigP.items(), key=lambda x: x[1]):
        u = adj[v][k]
        w = ev(v, k)
        cols.append([phi[v][i] + w[i] - phi[u][i] for i in range(rJ)])
    M = Matrix(cols).T
    S = smith_normal_form(M)
    diag = [S[i, i] for i in range(min(S.shape))]
    ok = len(cols) <= rJ and all(abs(x) == 1 for x in diag)
    return rJ - len(cols), ok


def main():
    j, d, kmax = [int(x) for x in sys.argv[1:4]]
    maxstates = int(sys.argv[4]) if len(sys.argv) > 4 else 500000
    Cj, Cj1 = core(j), core(j + 1)
    stats = Counter()
    bad = 0
    for al, ta in classes(d):
        nbK = relabel(cover(al, ta, j + 1))
        level = {canon(nbK): nbK}
        seen = set(level)
        n = 0
        for k in range(1, kmax + 1):
            nxt = {}
            for nb in level.values():
                V = len(nb)
                for u in range(V):
                    for v in range(u + 1, V):
                        nbJ = relabel(fold_with(nb, [(u, v)]))
                        c = canon(nbJ)
                        if c in seen:
                            continue
                        seen.add(c)
                        d1, _, _ = cover_degree(nbJ, Cj1)
                        if d1 != d:
                            continue
                        d0, order, adj = cover_degree(nbJ, Cj)
                        if d0 == d:
                            if inside(nbJ, Cj):
                                ex, ok = h1_split(nbJ, order, adj)
                                assert ex == 0 and ok  # sanity: J = K'
                                stats[k, 'J=K\''] += 1
                            else:
                                ex, ok = h1_split(nbJ, order, adj)
                                PA, PB = transported_set(order, adj, j)
                                lw = law0(PA, PB, kmax + 1)
                                stats[k, ex, ok, 'law', lw] += 1
                                # (O'): law <= number of rank drops = k - ex
                                if lw is None or lw > k - ex:
                                    stats['O-prime violated'] += 1
                                    print('O-PRIME VIOLATED alpha', al,
                                          'tau', ta, 'level', k, 'ex', ex,
                                          'law', lw, 'J', nbJ)
                                if not ok:
                                    bad += 1
                                    print('NOT SPLIT alpha', al, 'tau', ta,
                                          'level', k, 'law(K\')', lw,
                                          'minimal' if lw == k else '',
                                          'J', nbJ)
                            continue
                        nxt[c] = nbJ
                        n += 1
                        if n > maxstates:
                            break
            level = nxt
    print('j', j, 'd', d, 'kmax', kmax, 'not split', bad)
    print(sorted(stats.items(), key=str))


if __name__ == '__main__':
    main()
