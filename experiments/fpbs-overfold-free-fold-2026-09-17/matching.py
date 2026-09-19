"""Shape of the fold closure of one realizable overfold seed.

For a seed (u, v) of type T (a finite tree of pairs of C_{j+1}), the
first wave of the closure is the lift of T at (u, v): |T| vertex pairs of
Gamma_K.  'Matching' means the closure is exactly this first wave with
pairwise disjoint pairs (all classes of size <= 2, |T| classes of size 2).
If the closure is a matching, Gamma_K / (pairs) is already folded and
rk J = rk K + 1 (no rank drop).
Records (matching?, max class size, rbar(J) - d) for all realizable
overfold single seeds over all K classes of size d.
Usage: python3 matching.py j d
"""
import sys
from collections import Counter
from freefold import core, cover, label, cover_degree, freeze
from foldlib import Fold
from bfs_free import classes


def pair_tree_size(C, c, cp):
    """Number of vertices of the component of (c, cp) in C x_R C."""
    seen = {(c, cp)}
    st = [(c, cp)]
    while st:
        x, y = st.pop()
        for k, x2 in C[x].items():
            y2 = C[y].get(k)
            if y2 is not None and (x2, y2) not in seen:
                seen.add((x2, y2))
                st.append((x2, y2))
    return len({frozenset(p) for p in seen})  # unordered pairs


def closure(nb, u, v):
    F = Fold()
    for _ in range(len(nb)):
        F.new()
    F._pending = []
    for x in range(len(nb)):
        for k, y in nb[x].items():
            if k[1] == 1:
                F._link(x, k, y)
                F._link(y, (k[0], -1), x)
    F.fold()
    F.union(u, v)
    cls = Counter(F.find(x) for x in range(len(nb)))
    return cls, freeze(F, [0])


def main():
    j, d = int(sys.argv[1]), int(sys.argv[2])
    Cj, Cj1 = core(j), core(j + 1)
    iota = label(Cj1, Cj)
    st = Counter()
    for al, ta in classes(d):
        nbK = cover(al, ta, j + 1)
        lab = label(nbK, Cj1)
        V = len(nbK)
        for u in range(V):
            for v in range(u + 1, V):
                if lab[u] == lab[v] or iota[lab[u]] == iota[lab[v]]:
                    continue
                cls, nbH = closure(nbK, u, v)
                d1, _, _ = cover_degree(nbH, Cj1)
                if d1 != d:
                    continue
                sizes = Counter(cls.values())
                T = pair_tree_size(Cj1, lab[u], lab[v])
                match = (max(sizes) <= 2 and sizes.get(2, 0) == T)
                E = sum(len(x) for x in nbH) // 2
                rb = E - len(nbH)
                st[match, max(sizes), rb - d] += 1
    print('j', j, 'd', d, '(matching, max class, rbar(J)-d): count')
    for k, n in sorted(st.items(), key=str):
        print(' ', k, n)


if __name__ == '__main__':
    main()
