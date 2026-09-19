"""Q-free search for deep_j < law_j: fold overfold seeds in the free group.

Setting (see research/fpbs-mal-overfold-merges-never-help.md, relative-rank
form).  Fix j >= 1, L_j = <a, t_j>, C_j its Stallings core.

Input: a transitive L_{j+1}-set of size d (perms alpha for a, tau for
t_{j+1}); K = Stab(0) <= L_{j+1}.  Gamma_K is the degree-d cover of C_{j+1}.
A seed is a pair of vertices (x,c), (y,c') of Gamma_K; it adds one element
g = u u'^{-1} to pi_1, and it is overfold iff iota(c) != iota(c').

For seeds s_1..s_k we fold Gamma_K freely (no Q) and get the Stallings
graph of H = <K, g_1..g_k>.  We compute
  K_H  = H cap L_{j+1}  (pullback with C_{j+1}, base component),
  K'_H = H cap L_j      (pullback with C_j, base component).
A hit is: K'_H of finite index in L_j (the base component covers C_j) and
[L_j : K'_H] = [L_{j+1} : K_H] (L_{j+1} transitive on L_j / K'_H).

For a hit, M. Hall's theorem (free groups are LERF) gives a finite-index
S >= H with S cap L_j = K'_H: avoid the finitely many coset representatives
of K'_H in L_j outside K'_H.  On Q = L/S the component of Gamma_{j+1}(Q) at
the base point is Gamma_{K_H}, the seeds s_i are same-fibre seeds, and
<K_H, g_i> = H contains K'_H, so the closure contains ker(m) over that
component.  Hence deep_j(Q) <= law_j(Q) - law(comp) + k, and a hit with
law(comp) = rk(K'_H : K_H) > k refutes (O).

law(comp) is computed exactly: transport the L_j-set L_j/K'_H to an L-set P
(a acts as a, b acts as t_j); then rk(K'_H : K_H) = law_0(P), computed with
the existing exact code.
"""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-depth-overfolding-2026-09-17'))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-overfold-relative-rank-2026-09-17'))
from foldlib import Fold, t, A, depth_graphs, contains_kernel  # noqa: E402
from exact_search import search  # noqa: E402
from struct_search import seeds_of  # noqa: E402

KEYS = [('a', 1), ('a', -1), ('b', 1), ('b', -1)]


def freeze(F, base_ids):
    """Folded graph -> (nb list of dicts), with base_ids listed first."""
    roots = F.roots()
    idx = {}
    for x in base_ids:
        r = F.find(x)
        if r not in idx:
            idx[r] = len(idx)
    for r in roots:
        if r not in idx:
            idx[r] = len(idx)
    nb = [dict() for _ in range(len(idx))]
    for r in roots:
        for k, v in F.adj[r].items():
            nb[idx[r]][k] = idx[F.find(v)]
    return nb


def core(j):
    F = Fold()
    F.new()
    F._pending = []
    F.add_path(0, A, 0)
    F.add_path(0, t(j), 0)
    return freeze(F, [0])


def cover(alpha, tau, j1):
    """Stallings graph of the L_{j1}-set (alpha = a, tau = t_{j1})."""
    d = len(alpha)
    F = Fold()
    for _ in range(d):
        F.new()
    F._pending = []
    w = t(j1)
    for i in range(d):
        F.add_path(i, A, alpha[i])
        F.add_path(i, w, tau[i])
    return freeze(F, list(range(d)))


def label(nb, C):
    """Immersion nb -> C sending vertex 0 to base 0 (BFS)."""
    lab = [None] * len(nb)
    lab[0] = 0
    st = [0]
    while st:
        v = st.pop()
        for k, u in nb[v].items():
            cu = C[lab[v]][k]
            if lab[u] is None:
                lab[u] = cu
                st.append(u)
            else:
                assert lab[u] == cu
    return lab


def fold_with(nb, pairs):
    F = Fold()
    for _ in range(len(nb)):
        F.new()
    F._pending = []
    for v in range(len(nb)):
        for k, u in nb[v].items():
            if k[1] == 1:
                F._link(v, k, u)
                F._link(u, (k[0], -1), v)
    F.fold()
    for (u, v) in pairs:
        F.union(u, v)
    return freeze(F, [0])


def pullback(nb, C):
    """Base component of nb x_R C.  Returns (vertex list, adjacency)."""
    start = (0, 0)
    seen = {start: 0}
    order = [start]
    adj = [dict()]
    i = 0
    while i < len(order):
        h, c = order[i]
        for k, c2 in C[c].items():
            h2 = nb[h].get(k)
            if h2 is None:
                continue
            p = (h2, c2)
            if p not in seen:
                seen[p] = len(order)
                order.append(p)
                adj.append(dict())
            adj[i][k] = seen[p]
        i += 1
    return order, adj


def cover_degree(nb, C):
    """[L_C : H cap L_C] if the base component covers C, else None."""
    order, adj = pullback(nb, C)
    for i, (h, c) in enumerate(order):
        if len(adj[i]) != len(C[c]):
            return None, None, None
    assert len(order) % len(C) == 0
    return len(order) // len(C), order, adj


def transported_set(order, adj, j):
    """L-set P: fibre over base of C_j, a -> a-edge, b -> read t_j."""
    pts = [i for i, (h, c) in enumerate(order) if c == 0]
    pos = {p: n for n, p in enumerate(pts)}

    def read(i, w):
        for k in w:
            i = adj[i][k]
        return i
    PA = [pos[read(p, A)] for p in pts]
    PB = [pos[read(p, t(j))] for p in pts]
    return PA, PB


def law0(PA, PB, maxlaw):
    """rk(Stab_L(0) : Stab_{L_1}(0)) for an L_1-transitive L-set."""
    Gj, G, m = depth_graphs(PA, PB, 0)
    kerok = lambda cls: contains_kernel(G, cls, m)  # noqa: E731
    if kerok(list(range(G.V))):
        return 0
    allp, lawp = seeds_of(G, m)
    k, _ = search(G, m, lawp, kerok, maxlaw)
    return k


def analyse(nbK, pairs, Cj, Cj1, j, maxlaw):
    """Fold seeds into Gamma_K; return None or (d_{j+1}, d_j, law)."""
    nbH = fold_with(nbK, pairs)
    d1, _, _ = cover_degree(nbH, Cj1)
    if d1 is None:
        return None
    d0, order, adj = cover_degree(nbH, Cj)
    if d0 is None:
        return ('infidx', d1, d0)
    if d0 != d1:
        return ('nt', d1, d0)
    PA, PB = transported_set(order, adj, j)
    return ('hit', d1, d0, law0(PA, PB, maxlaw), len(nbH))
