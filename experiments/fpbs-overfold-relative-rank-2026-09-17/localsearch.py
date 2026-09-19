"""Local search for deep_j(Q) < law_j(Q): fix k = law - 1 seeds (all
same-fibre types allowed), minimise the number of kernel defects
ker_count (0 means the closure contains ker(m)) by single-seed swaps with
random restarts.  Heuristic: a 0 is a certified counterexample (the witness
is re-checked), failure proves nothing.
Usage: python3 localsearch.py j mode(cayley|rand) arg restarts steps
  cayley: arg = maxorder;  rand: arg = n (20 random transitive Q, seed 11)
"""
import random
import sys
from struct_search import cayley, seeds_of, perms
from multiorbit import law_by_component, ker_count, comps
from foldlib import depth_graphs, closure, contains_kernel, random_q
from exact_search import transitive


def attempt(G, m, allp, k, rng, steps):
    cur = [rng.choice(allp) for _ in range(k)]
    val = ker_count(G, closure(G, cur), m)
    for _ in range(steps):
        if val == 0:
            return cur
        i = rng.randrange(k)
        s = rng.choice(allp)
        trial = cur[:i] + [s] + cur[i + 1:]
        v2 = ker_count(G, closure(G, trial), m)
        if v2 <= val:
            cur, val = trial, v2
    return cur if val == 0 else None


def run(PA, PB, j, restarts, steps, rng, tag):
    Gj, G, m = depth_graphs(PA, PB, j)
    allp, lawp = seeds_of(G, m)
    law = law_by_component(G, Gj, m, lawp, 8)
    if law is None or law < 2:
        return
    best = None
    for _ in range(restarts):
        w = attempt(G, m, allp, law - 1, rng, steps)
        if w is not None:
            assert contains_kernel(G, closure(G, w), m)
            best = w
            break
    cj = comps(Gj)
    print(tag, 'n', len(PA), 'Lj-orbits', len(set(cj)), 'law', law,
          'found', 'FLAG deep<law witness %s' % best if best else 'none')
    sys.stdout.flush()


def main():
    j, mode, arg, restarts, steps = (int(sys.argv[1]), sys.argv[2],
                                     int(sys.argv[3]), int(sys.argv[4]),
                                     int(sys.argv[5]))
    rng = random.Random(5)
    if mode == 'rand':
        r2 = random.Random(11)
        done = 0
        while done < 20:
            PA, PB = random_q(arg, r2)
            if transitive(PA, PB):
                done += 1
                run(PA, PB, j, restarts, steps, rng, 'rand')
        return
    seen = set()
    for d in (3, 4, 5):
        for al in perms(d):
            for be in perms(d):
                r = cayley(al, be, arg)
                if r is None or (tuple(r[0]), tuple(r[1])) in seen:
                    continue
                seen.add((tuple(r[0]), tuple(r[1])))
                run(r[0], r[1], j, restarts, steps, rng, 'cayley %s %s' % (al, be))


if __name__ == '__main__':
    main()
