"""Exact test of deep_j(Q) <= cap for one Cayley action, all same-fibre seeds.
Prints law (sum of component laws), number of seed classes, and the least
k <= cap reaching a partition containing ker(m), or 'none <= cap'.
Usage: python3 exact_multi.py j cap a-perm b-perm
"""
import sys
import time
from struct_search import cayley, seeds_of
from multiorbit import law_by_component, comps
from foldlib import depth_graphs, contains_kernel
from exact_search import search

j = int(sys.argv[1])
cap = int(sys.argv[2])
al = tuple(int(x) for x in sys.argv[3].split(','))
be = tuple(int(x) for x in sys.argv[4].split(','))
PA, PB = cayley(al, be, 10 ** 6)
Gj, G, m = depth_graphs(PA, PB, j)
allp, lawp = seeds_of(G, m)
law = law_by_component(G, Gj, m, lawp, 6)
t0 = time.time()
k, wit = search(G, m, allp, lambda c: contains_kernel(G, c, m), cap)
cj = comps(Gj)
cross = 0 if wit is None else sum(1 for (u, v) in wit if cj[m[u]] != cj[m[v]])
print('order', len(PA), 'j', j, 'Lj-orbits', len(set(cj)), 'V', G.V, '->', Gj.V,
      'seed classes', len(allp), 'law', law,
      'deep', k if k is not None else 'none <= %d' % cap,
      'cross-orbit seeds in witness', cross, 'secs', round(time.time() - t0, 1))
