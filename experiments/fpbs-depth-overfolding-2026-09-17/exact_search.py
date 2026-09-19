"""Exact deep_j(Q) versus law_j(Q) on small random Q.

deep_j(Q) = least number of same-fibre merges of Gamma_{j+1}(Q) whose fold
closure contains ker(m: Gamma_{j+1} -> Gamma_j).
law_j(Q)  = least number of lawful merges (pairs inside ker) whose closure
equals ker (closures of lawful seeds always stay inside ker, since the
quotient by ker is the folded graph Gamma_j).
Search: breadth first over the distinct partitions reached with k seeds
(seeds deduplicated by their single-seed closure).
Usage: python3 exact_search.py n j trials seed [maxlevel]
"""
import random
import sys
from foldlib import random_q, depth_graphs, closure, contains_kernel


def canon(cls):
    """Relabel classes by first occurrence, so equal partitions compare equal."""
    first = {}
    return tuple(first.setdefault(c, len(first)) for c in cls)


def transitive(PA, PB):
    n = len(PA)
    seen = {0}
    st = [0]
    while st:
        p = st.pop()
        for q in (PA[p], PB[p], PA.index(p), PB.index(p)):
            if q not in seen:
                seen.add(q)
                st.append(q)
    return len(seen) == n


def search(G, m, seeds, goal, maxlevel):
    """Least k such that some k seeds reach a partition satisfying goal."""
    level = {canon(list(range(G.V))): []}
    for k in range(1, maxlevel + 1):
        nxt = {}
        for part, chosen in level.items():
            for s in seeds:
                cls = closure(G, chosen + [s])
                c = canon(cls)
                if c in nxt or c == part:
                    continue
                if goal(cls):
                    return k, chosen + [s]
                nxt[c] = chosen + [s]
        level = nxt
        if not level:
            return None, None
    return None, None


def main():
    n, j, trials, seed = [int(x) for x in sys.argv[1:5]]
    maxlevel = int(sys.argv[5]) if len(sys.argv) > 5 else 6
    rng = random.Random(seed)
    done = 0
    while done < trials:
        PA, PB = random_q(n, rng)
        if not transitive(PA, PB):
            continue
        done += 1
        Gj, Gj1, m = depth_graphs(PA, PB, j)
        fib = {}
        for v in range(Gj1.V):
            fib.setdefault(Gj1.over[v], []).append(v)
        allp, lawp = {}, {}
        for vs in fib.values():
            for a in range(len(vs)):
                for b in range(a + 1, len(vs)):
                    u, v = vs[a], vs[b]
                    c = canon(closure(Gj1, [(u, v)]))
                    if m[u] == m[v]:
                        lawp.setdefault(c, (u, v))
                    allp.setdefault(c, (u, v))
        kerok = lambda cls: contains_kernel(Gj1, cls, m)
        law, _ = search(Gj1, m, list(lawp.values()), kerok, maxlevel)
        deep, wit = search(Gj1, m, list(allp.values()), kerok, maxlevel)
        nover = sum(1 for (u, v) in (wit or []) if m[u] != m[v])
        print('n', n, 'j', j, 'V', Gj1.V, '->', Gj.V,
              'seed-classes all/lawful', len(allp), len(lawp),
              'law', law, 'deep', deep, 'overfold seeds in witness', nover,
              'FLAG deep<law' if (law and deep and deep < law) else '')
        sys.stdout.flush()


if __name__ == '__main__':
    main()
