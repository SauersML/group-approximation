"""deep_j versus law_j when Q has SEVERAL L_j-orbits.

Lawful merges never leave the preimage of one component of Gamma_j(Q), so
law_j(Q) = sum over components C of Gamma_j(Q) of law(C) (exact BFS per C).
Overfold merges may join vertices over the same point of Q lying over
DIFFERENT components of Gamma_j; this regime was absent from the random
census (random Q are L_j-transitive).  We bound deep_j(Q) above by greedy
search over all same-fibre seeds, with random tie-breaking restarts.
Usage: python3 multiorbit.py j maxorder restarts [maxlaw]
"""
import random
import sys
from struct_search import cayley, seeds_of, perms
from foldlib import depth_graphs, closure, contains_kernel
from exact_search import search


def comps(G):
    par = list(range(G.V))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for v in range(G.V):
        for u in G.nb[v].values():
            par[f(u)] = f(v)
    return [f(v) for v in range(G.V)]


def ker_count(G, cls, m):
    """number of vertices v not in the class of the first vertex of its m-fibre"""
    first = {}
    bad = 0
    for v in range(G.V):
        f = first.setdefault(m[v], v)
        if cls[f] != cls[v]:
            bad += 1
    return bad


def law_by_component(G, Gj, m, lawp, maxlaw):
    cj = comps(Gj)
    tot = 0
    for c in sorted(set(cj)):
        vs = [v for v in range(G.V) if cj[m[v]] == c]
        seeds = [(u, v) for (u, v) in lawp if cj[m[u]] == c]

        def goal(cls, vs=vs):
            first = {}
            for v in vs:
                f = first.setdefault(m[v], v)
                if cls[f] != cls[v]:
                    return False
            return True
        if goal(list(range(G.V))):
            continue
        k, _ = search(G, m, seeds, goal, maxlaw)
        if k is None:
            return None
        tot += k
    return tot


def greedy(G, m, allp, rng):
    chosen = []
    cls = list(range(G.V))
    while ker_count(G, cls, m) > 0:
        best, bestv = [], None
        for s in allp:
            c2 = closure(G, chosen + [s])
            val = (ker_count(G, c2, m), len(set(c2)))
            if bestv is None or val < bestv:
                best, bestv = [s], val
            elif val == bestv:
                best.append(s)
        s = rng.choice(best)
        chosen.append(s)
        cls = closure(G, chosen)
    return len(chosen), chosen


def main():
    j = int(sys.argv[1])
    maxorder = int(sys.argv[2])
    restarts = int(sys.argv[3])
    maxlaw = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    rng = random.Random(1)
    seen = set()
    for d in (3, 4, 5):
        for al in perms(d):
            for be in perms(d):
                r = cayley(al, be, maxorder)
                if r is None or (tuple(r[0]), tuple(r[1])) in seen:
                    continue
                seen.add((tuple(r[0]), tuple(r[1])))
                PA, PB = r
                Gj, G, m = depth_graphs(PA, PB, j)
                ncj = len(set(comps(Gj)))
                if ncj < 2:
                    continue
                allp, lawp = seeds_of(G, m)
                law = law_by_component(G, Gj, m, lawp, maxlaw)
                gd = min(greedy(G, m, allp, rng)[0] for _ in range(restarts))
                flag = 'FLAG deep<law' if (law is not None and gd < law) else ''
                print('order', len(PA), 'a', al, 'b', be, 'Lj-orbits', ncj,
                      'V', G.V, '->', Gj.V, 'law', law, 'greedy-deep', gd, flag)
                sys.stdout.flush()


if __name__ == '__main__':
    main()
