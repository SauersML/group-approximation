"""Exact Q-universal search for deep_j < law_j on L_{j+1}-transitive
components, by breadth-first search over free folds (see freefold.py).

For every transitive L_{j+1}-set of size d (up to isomorphism), K = Stab(0):
  level 0 state = Gamma_K; a move merges two vertices of the current folded
  graph (a same-fibre seed) and folds.  States are based folded graphs, i.e.
  subgroups J = <K, g_1..g_k>, deduplicated by canonical form.
  Pruned: states with J cap L_{j+1} != K (then no Q has this component).
  Hit: J cap L_j = K' of finite index d in L_j (hits are terminal: further
  seeds keep K').  For each hit, law(K') = rk(K':K) is computed exactly.
Output per K: the least level at which each K' is hit, against law(K').
A hit at level k with law(K') > k refutes (O) (Q-universal: every finite Q
whose base component is this one; S from M. Hall's theorem).
Usage: python3 bfs_free.py j d kmax [maxlaw] [maxstates]
"""
import itertools
import sys
from collections import Counter
from freefold import (core, cover, fold_with, cover_degree, transported_set,
                      law0, KEYS)
from exhaustive import cycle_type_reps, canon_form


def canon(nb):
    lab = {0: 0}
    order = [0]
    i = 0
    while i < len(order):
        v = order[i]
        for k in KEYS:
            u = nb[v].get(k)
            if u is not None and u not in lab:
                lab[u] = len(order)
                order.append(u)
        i += 1
    return tuple(tuple(lab.get(nb[v].get(k), -1) for k in KEYS)
                 for v in order)


def relabel(nb):
    """Return nb relabelled in canonical order (base 0)."""
    c = canon(nb)
    return [{k: c[v][i] for i, k in enumerate(KEYS) if c[v][i] >= 0}
            for v in range(len(c))]


def classes(d):
    seen = set()
    for PA in cycle_type_reps(d):
        for PB in itertools.permutations(range(d)):
            f = canon_form(PA, list(PB))
            if f is None or f in seen:
                continue
            seen.add(f)
            yield PA, list(PB)


def explore(al, ta, j, kmax, maxlaw, maxstates, Cj, Cj1):
    d = len(al)
    nbK = relabel(cover(al, ta, j + 1))
    level = {canon(nbK): nbK}
    seen = set(level)
    hits = {}  # canon of K' pullback -> (k, law)
    flags = []
    nstates = 0
    for k in range(1, kmax + 1):
        nxt = {}
        for nb in level.values():
            V = len(nb)
            for u in range(V):
                for v in range(u + 1, V):
                    nbJ = relabel(fold_with(nb, [(u, v)]))
                    c = canon(nbJ)
                    if c in seen:
                        continue
                    seen.add(c)
                    d1, _, _ = cover_degree(nbJ, Cj1)
                    if d1 != d:
                        continue
                    d0, order, adj = cover_degree(nbJ, Cj)
                    if d0 is not None and d0 == d:
                        PA, PB = transported_set(order, adj, j)
                        key = canon_form(PA, PB)
                        if key not in hits:
                            lw = law0(PA, PB, maxlaw)
                            hits[key] = (k, lw)
                            if lw is None or lw > k:
                                flags.append((k, lw, u, v, PA, PB))
                        continue
                    nxt[c] = nbJ
                    nstates += 1
                    if nstates > maxstates:
                        return hits, flags, 'capped'
        level = nxt
        if not level:
            break
    return hits, flags, 'ok'


def main():
    j, d, kmax = [int(x) for x in sys.argv[1:4]]
    maxlaw = int(sys.argv[4]) if len(sys.argv) > 4 else 5
    maxstates = int(sys.argv[5]) if len(sys.argv) > 5 else 200000
    Cj, Cj1 = core(j), core(j + 1)
    total = Counter()
    nclass = 0
    for al, ta in classes(d):
        nclass += 1
        hits, flags, st = explore(al, ta, j, kmax, maxlaw, maxstates, Cj, Cj1)
        for (k, lw) in hits.values():
            total[k, lw] += 1
        print('class', nclass, 'alpha', al, 'tau', ta, st,
              'hits (level,law):', sorted(Counter(hits.values()).items()),
              'FLAGS' if flags else '')
        for f in flags:
            print('  FLAG deep<=%d < law=%s  seed %s %s  P a=%s b=%s'
                  % (f[0], f[1], f[2], f[3], f[4], f[5]))
        sys.stdout.flush()
    print('classes', nclass, 'total hits by (level, law):',
          sorted(total.items()))


if __name__ == '__main__':
    main()
