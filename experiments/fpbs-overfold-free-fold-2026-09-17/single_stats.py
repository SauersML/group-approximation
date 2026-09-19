"""Statistics of realizable single overfold seeds (all classes of size d).

For each overfold seed on Gamma_K with J = <K, g>, J cap L_{j+1} = K:
record (rbar(J) - d, index class of J cap L_j) where the index class is
'inf' (base component of Gamma_J x C_j is not a cover) or the degree.
rbar(J) = rk J - 1 = -chi(Gamma_J); rbar(J) - d is 1 (free product
K * <g>) or 0 (one rank-dropping fold).
Usage: python3 single_stats.py j d
"""
import sys
from collections import Counter
from freefold import core, cover, label, fold_with, cover_degree
from bfs_free import classes


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
                nbH = fold_with(nbK, [(u, v)])
                d1, _, _ = cover_degree(nbH, Cj1)
                if d1 != d:
                    continue
                E = sum(len(x) for x in nbH) // 2
                rb = E - len(nbH)
                d0, _, _ = cover_degree(nbH, Cj)
                st[rb - d, 'inf' if d0 is None else d0] += 1
    print('j', j, 'd', d, sorted(st.items(), key=str))


if __name__ == '__main__':
    main()
