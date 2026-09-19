"""Compare law_j(Q) with full_j(Q) = least number of same-fibre seeds whose
fold closure collapses every fibre of Gamma_{j+1}(Q) -> Q to a point (the TOP
closed family; deep_j <= full_j).  A level with full_j < law_j refutes the
overfold claim outright.  Exact BFS up to cap for full_j, greedy upper bound
beyond.
Usage: python3 top_vs_law.py j cap mode(rand|cayley) [n trials seed]
"""
import random
import sys
from struct_search import cayley, seeds_of, perms
from multiorbit import law_by_component, greedy
from foldlib import depth_graphs, random_q
from exact_search import search, transitive


def over_collapsed(G):
    def goal(cls):
        first = {}
        for v in range(G.V):
            f = first.setdefault(G.over[v], v)
            if cls[f] != cls[v]:
                return False
        return True
    return goal


def greedy_top(G, allp, rng, restarts):
    from foldlib import closure
    goal = over_collapsed(G)
    best = None
    for _ in range(restarts):
        chosen, cls = [], list(range(G.V))
        while not goal(cls):
            cands, bv = [], None
            for s in allp:
                c2 = closure(G, chosen + [s])
                val = len(set(c2))
                if bv is None or val < bv:
                    cands, bv = [s], val
                elif val == bv:
                    cands.append(s)
            chosen.append(rng.choice(cands))
            cls = closure(G, chosen)
        best = len(chosen) if best is None else min(best, len(chosen))
    return best


def run(PA, PB, j, cap, rng, tag):
    Gj, G, m = depth_graphs(PA, PB, j)
    allp, lawp = seeds_of(G, m)
    law = law_by_component(G, Gj, m, lawp, 6)
    full, _ = search(G, m, allp, over_collapsed(G), cap)
    gt = greedy_top(G, allp, rng, 3) if full is None else full
    flag = 'FLAG full<law' if (law is not None and gt < law) else ''
    print(tag, 'n', len(PA), 'j', j, 'V', G.V, '->', Gj.V, 'law', law,
          'full', full if full is not None else '>%d (greedy %d)' % (cap, gt), flag)
    sys.stdout.flush()


def main():
    j, cap, mode = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    rng = random.Random(7)
    if mode == 'rand':
        n, trials, seed = [int(x) for x in sys.argv[4:7]]
        r2 = random.Random(seed)
        done = 0
        while done < trials:
            PA, PB = random_q(n, r2)
            if not transitive(PA, PB):
                continue
            done += 1
            run(PA, PB, j, cap, rng, 'rand')
    else:
        maxorder = int(sys.argv[4])
        seen = set()
        for d in (3, 4, 5):
            for al in perms(d):
                for be in perms(d):
                    r = cayley(al, be, maxorder)
                    if r is None or (tuple(r[0]), tuple(r[1])) in seen:
                        continue
                    seen.add((tuple(r[0]), tuple(r[1])))
                    run(r[0], r[1], j, cap, rng, 'cayley %s %s' % (al, be))


if __name__ == '__main__':
    main()
