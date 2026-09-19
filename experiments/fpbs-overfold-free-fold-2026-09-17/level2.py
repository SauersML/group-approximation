"""Two-seed free-fold search on the components with law >= minlaw.

Enumerate all L-sets P of size d (up to iso) that are L_1-transitive with
law_0(P) >= minlaw; transport to level j: K = Stab_{L_{j+1}}(0) where
a acts as P(a) and t_{j+1} acts as P(t_1) (t_1 = b a b^-2).  Run the exact
free-fold BFS of bfs_free.explore to depth kmax (realizable states only,
i.e. J cap L_{j+1} = K).  A hit at level k whose K' has law > k refutes (O).
Usage: python3 level2.py j d kmax [minlaw] [maxstates]
"""
import sys
from collections import Counter
from freefold import core, law0
from foldlib import act, inverse_perm, t, A, depth_graphs  # noqa: F401
from multiorbit import comps
from bfs_free import classes, explore
from exhaustive import canon_form


def main():
    j, d, kmax = [int(x) for x in sys.argv[1:4]]
    minlaw = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    maxstates = int(sys.argv[5]) if len(sys.argv) > 5 else 2000000
    Cj, Cj1 = core(j), core(j + 1)
    seenK = set()
    total = Counter()
    for PA, PB in classes(d):
        Gj, G, m = depth_graphs(PA, PB, 0)
        if len(set(comps(G))) != 1:
            continue
        lw = law0(PA, PB, minlaw + 2)
        if lw is None or lw < minlaw:
            continue
        IA, IB = inverse_perm(PA), inverse_perm(PB)
        ta = [act(p, t(1), PA, PB, IA, IB) for p in range(d)]
        key = canon_form(PA, ta)
        if key in seenK:
            continue
        seenK.add(key)
        hits, flags, st = explore(PA, ta, j, kmax, minlaw + 2, maxstates,
                                  Cj, Cj1)
        for v in hits.values():
            total[v] += 1
        print('P a', PA, 'b', PB, 'law', lw, 'K: alpha', PA, 'tau', ta, st,
              'hits (level,law):', sorted(Counter(hits.values()).items()),
              'FLAGS %d' % len(flags) if flags else '')
        for f in flags:
            print('  FLAG deep<=%d < law=%s  seed %s %s  P a=%s b=%s'
                  % (f[0], f[1], f[2], f[3], f[4], f[5]))
        sys.stdout.flush()
    print('j', j, 'd', d, 'K classes', len(seenK), 'total hits',
          sorted(total.items()))


if __name__ == '__main__':
    main()
