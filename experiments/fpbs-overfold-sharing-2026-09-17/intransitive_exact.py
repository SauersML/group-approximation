"""Exact deep_j(Q) versus law_j(Q) on L-transitive Q whose L_j-restriction is
intransitive (at least two L_j-orbits).

The random levels of exact_search.py almost always have L_j transitive, so
cross-orbit merges (same-fibre pairs of Gamma_{j+1}(Q) whose two vertices map
into different L_j-components of Gamma_j(Q)) never had the chance to serve two
orbits at once.  This script samples only levels where they can.

Reuses foldlib.py and the search of exact_search.py.
Usage: python3 intransitive_exact.py n j trials seed [maxlevel] [minorbits]
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-depth-overfolding-2026-09-17'))

from foldlib import random_q, depth_graphs, closure, contains_kernel, t, act, inverse_perm  # noqa: E402
from exact_search import canon, transitive, search  # noqa: E402


def orbits(PA, PB, gens):
    n = len(PA)
    IA, IB = inverse_perm(PA), inverse_perm(PB)
    perms = []
    for w in gens:
        P = [act(p, w, PA, PB, IA, IB) for p in range(n)]
        perms.append(P)
        perms.append(inverse_perm(P))
    lab = [-1] * n
    k = 0
    for s in range(n):
        if lab[s] >= 0:
            continue
        lab[s] = k
        st = [s]
        while st:
            p = st.pop()
            for P in perms:
                q = P[p]
                if lab[q] < 0:
                    lab[q] = k
                    st.append(q)
        k += 1
    return k, lab


def analyse(PA, PB, j, maxlevel):
    Gj, Gj1, m = depth_graphs(PA, PB, j)
    fib = {}
    for v in range(Gj1.V):
        fib.setdefault(Gj1.over[v], []).append(v)
    # component of each vertex of Gamma_j (an L_j-orbit)
    nj, labj = orbits(PA, PB, [[('a', 1)], t(j)])
    allp, lawp = {}, {}
    ncross = 0
    for vs in fib.values():
        for x in range(len(vs)):
            for y in range(x + 1, len(vs)):
                u, v = vs[x], vs[y]
                c = canon(closure(Gj1, [(u, v)]))
                if m[u] == m[v]:
                    lawp.setdefault(c, (u, v))
                allp.setdefault(c, (u, v))
    kerok = lambda cls: contains_kernel(Gj1, cls, m)
    law, lw = search(Gj1, m, list(lawp.values()), kerok, maxlevel)
    deep, dw = search(Gj1, m, list(allp.values()), kerok, maxlevel)
    nover = sum(1 for (u, v) in (dw or []) if m[u] != m[v])
    return dict(V=Gj1.V, Vj=Gj.V, nj=nj, nall=len(allp), nlaw=len(lawp),
                law=law, deep=deep, nover=nover, wit=dw, lawwit=lw)


def main():
    n, j, trials, seed = [int(x) for x in sys.argv[1:5]]
    maxlevel = int(sys.argv[5]) if len(sys.argv) > 5 else 6
    minorb = int(sys.argv[6]) if len(sys.argv) > 6 else 2
    rng = random.Random(seed)
    done = tries = 0
    while done < trials and tries < 10 ** 7:
        tries += 1
        PA, PB = random_q(n, rng)
        if not transitive(PA, PB):
            continue
        nj, _ = orbits(PA, PB, [[('a', 1)], t(j)])
        if nj < minorb:
            continue
        done += 1
        r = analyse(PA, PB, j, maxlevel)
        flag = 'FLAG deep<law' if (r['law'] and r['deep'] and r['deep'] < r['law']) else ''
        print('n', n, 'j', j, 'PA', PA, 'PB', PB, 'Lj-orbits', nj,
              'V', r['V'], '->', r['Vj'], 'law', r['law'], 'deep', r['deep'],
              'overfold-in-witness', r['nover'], flag)
        sys.stdout.flush()


if __name__ == '__main__':
    main()
