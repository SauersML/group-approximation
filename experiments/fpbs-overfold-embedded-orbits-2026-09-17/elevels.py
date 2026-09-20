"""Embedded-orbit levels (condition (E)) for the overfold problem.

(E) at depth j: every component of Gamma_j(Q) maps injectively to Q under
`over`, i.e. no two vertices of one component of Gamma_j(Q) lie over the
same point of Q.  Equivalently O.u_c are pairwise disjoint for c in V(C_j),
for every L_j-orbit O (u_c = a word reading o -> c in the core C_j).

Functions
  core_size(j)            |V(C_j)| (Gamma_j of the one-point set)
  e_defect(PA, PB, j)     number of same-component same-point vertex pairs of
                          Gamma_j(Q); (E) holds iff it is 0
  good_mass(PA, PB, j)    fraction of Q lying in L_j-orbits whose component
                          of Gamma_j(Q) embeds
Usage: python3 elevels.py j n trials seed      (frequency of (E) on random Q)
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-depth-overfolding-2026-09-17'))
from foldlib import Graph, gamma, A, t, random_q  # noqa: E402


def graph_j(PA, PB, j):
    return Graph(gamma(PA, PB, [A, t(j)]), len(PA), PA, PB)


def components(G):
    lab = [-1] * G.V
    k = 0
    for s in range(G.V):
        if lab[s] >= 0:
            continue
        lab[s] = k
        st = [s]
        while st:
            v = st.pop()
            for u in G.nb[v].values():
                if lab[u] < 0:
                    lab[u] = k
                    st.append(u)
        k += 1
    return k, lab


def core_size(j):
    return graph_j([0], [0], j).V


def comp_defects(PA, PB, j):
    """Per component of Gamma_j(Q): (real points, defect pairs)."""
    G = graph_j(PA, PB, j)
    k, lab = components(G)
    seen = [dict() for _ in range(k)]
    reals = [0] * k
    defect = [0] * k
    for v in range(G.V):
        c = lab[v]
        if v < G.n:
            reals[c] += 1
        o = G.over[v]
        defect[c] += seen[c].get(o, 0)
        seen[c][o] = seen[c].get(o, 0) + 1
    return reals, defect


def e_defect(PA, PB, j):
    return sum(comp_defects(PA, PB, j)[1])


def good_mass(PA, PB, j):
    reals, defect = comp_defects(PA, PB, j)
    return sum(r for r, d in zip(reals, defect) if d == 0) / len(PA)


def transitive(PA, PB):
    n = len(PA)
    IA = [0] * n
    IB = [0] * n
    for i in range(n):
        IA[PA[i]] = i
        IB[PB[i]] = i
    seen = {0}
    st = [0]
    while st:
        p = st.pop()
        for q in (PA[p], PB[p], IA[p], IB[p]):
            if q not in seen:
                seen.add(q)
                st.append(q)
    return len(seen) == n


def main():
    j, n, trials, seed = [int(x) for x in sys.argv[1:5]]
    rng = random.Random(seed)
    print('j', j, '|V(C_j)|', core_size(j))
    cnt = 0
    tot = 0
    while tot < trials:
        PA, PB = random_q(n, rng)
        if not transitive(PA, PB):
            continue
        tot += 1
        if e_defect(PA, PB, j) == 0:
            cnt += 1
            print('E', PA, PB)
    print('transitive', tot, 'with (E)', cnt)


if __name__ == '__main__':
    main()
