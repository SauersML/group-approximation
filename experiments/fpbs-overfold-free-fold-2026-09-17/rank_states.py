"""Rank profile of realizable free-fold states.

For every K class of size d and every realizable state J (reached by k <= kmax
seeds with J cap L_{j+1} = K), record
  (k, rbar(J) - d, Gamma_J is a cover of the rose, J cap L_j finite index d).
Tests two statements:
  (R)  a realizable state with one overfold seed and d >= 2 has
       rbar(J) = d + 1 (J = K * <g>);
  (H)  rbar(J) = d (SHNC base-term equality) forces Gamma_J to be a
       d-vertex cover (J of finite index d, L_{j+1} transitive on L/J).
Usage: python3 rank_states.py j d kmax
"""
import sys
from collections import Counter
from freefold import core, cover, fold_with, cover_degree, label
from bfs_free import canon, relabel, classes


def main():
    j, d, kmax = [int(x) for x in sys.argv[1:4]]
    Cj, Cj1 = core(j), core(j + 1)
    iota = label(Cj1, Cj)
    st = Counter()
    for al, ta in classes(d):
        nbK = relabel(cover(al, ta, j + 1))
        labK = label(nbK, Cj1)
        level = {canon(nbK): (nbK, ())}
        seen = set(level)
        for k in range(1, kmax + 1):
            nxt = {}
            for nb, kinds in level.values():
                lab = labK  # used only at k = 1 (nb = Gamma_K)
                V = len(nb)
                for u in range(V):
                    for v in range(u + 1, V):
                        if k == 1:
                            kind = ('law' if iota[lab[u]] == iota[lab[v]]
                                    else 'over')
                        else:
                            kind = 'mixed'
                        nbJ = relabel(fold_with(nb, [(u, v)]))
                        c = canon(nbJ)
                        if c in seen:
                            continue
                        seen.add(c)
                        d1, _, _ = cover_degree(nbJ, Cj1)
                        if d1 != d:
                            continue
                        E = sum(len(x) for x in nbJ) // 2
                        rb = E - len(nbJ)
                        iscov = all(len(x) == 4 for x in nbJ)
                        d0, _, _ = cover_degree(nbJ, Cj)
                        st[k, kind, rb - d, iscov, d0 == d] += 1
                        if d0 != d:
                            nxt[c] = (nbJ, kinds + (kind,))
            level = nxt
    print('j', j, 'd', d, 'kmax', kmax)
    print('(k, kind, rbar(J)-d, cover, hit): count')
    for key, n in sorted(st.items(), key=str):
        print(' ', key, n)


if __name__ == '__main__':
    main()
