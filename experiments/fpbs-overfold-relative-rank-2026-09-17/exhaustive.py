"""EXHAUSTIVE exact check of deep_j(Q) = law_j(Q) over all transitive
F(a,b)-sets Q of size n, up to isomorphism (including Q that are not
L_j-transitive, which the random census never produced).

Isomorphism classes: canonical form = least BFS relabelling over start points.
law_j by exact BFS over lawful seeds (per component of Gamma_j, summed);
deep_j < law_j is then excluded by exact BFS over all same-fibre seeds up to
level law_j - 1.
Usage: python3 exhaustive.py n j [maxlaw]
"""
import itertools
import sys
from struct_search import seeds_of
from multiorbit import law_by_component, comps
from foldlib import depth_graphs, contains_kernel
from exact_search import search


def cycle_type_reps(n):
    reps = []

    def parts(k, mx):
        if k == 0:
            yield []
            return
        for p in range(min(k, mx), 0, -1):
            for rest in parts(k - p, p):
                yield [p] + rest
    for pa in parts(n, n):
        P, s = [0] * n, 0
        for L in pa:
            for i in range(L):
                P[s + i] = s + (i + 1) % L
            s += L
        reps.append(P)
    return reps


def canon_form(PA, PB):
    n = len(PA)
    IA = [0] * n
    IB = [0] * n
    for i in range(n):
        IA[PA[i]] = i
        IB[PB[i]] = i
    best = None
    for s in range(n):
        lab = {s: 0}
        order = [s]
        i = 0
        while i < len(order):
            p = order[i]
            for q in (PA[p], PB[p], IA[p], IB[p]):
                if q not in lab:
                    lab[q] = len(order)
                    order.append(q)
            i += 1
        if len(order) < n:
            return None
        f = tuple(lab[PA[p]] for p in order) + tuple(lab[PB[p]] for p in order)
        if best is None or f < best:
            best = f
    return best


def main():
    n, j = int(sys.argv[1]), int(sys.argv[2])
    maxlaw = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    classes = set()
    for PA in cycle_type_reps(n):
        for PB in itertools.permutations(range(n)):
            f = canon_form(PA, list(PB))
            if f is not None:
                classes.add(f)
    print('n', n, 'j', j, 'transitive classes', len(classes))
    hist, flags, nonLj = {}, 0, 0
    for f in sorted(classes):
        PA, PB = list(f[:n]), list(f[n:])
        Gj, G, m = depth_graphs(PA, PB, j)
        ncj = len(set(comps(Gj)))
        nonLj += ncj > 1
        allp, lawp = seeds_of(G, m)
        law = law_by_component(G, Gj, m, lawp, maxlaw)
        deep = law
        if law is not None and law >= 2:
            k, _ = search(G, m, allp, lambda c: contains_kernel(G, c, m), law - 1)
            if k is not None:
                deep = k
                flags += 1
                print('FLAG deep<law', PA, PB, 'law', law, 'deep', k)
        key = (law, deep)
        hist[key] = hist.get(key, 0) + 1
        sys.stdout.flush()
    print('histogram (law, deep): count', sorted(hist.items(), key=str))
    print('classes not L_j-transitive', nonLj, 'FLAGS', flags)


if __name__ == '__main__':
    main()
