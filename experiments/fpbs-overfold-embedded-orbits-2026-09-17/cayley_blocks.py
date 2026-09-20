"""Exact block tests (see blocks.py) on the Cayley level of G = <alpha, beta>,
restricted to blocks containing the L_j-orbit of the identity.  Left
multiplication by G is an automorphism of the marked Cayley graph that
permutes the L_j-orbits transitively, so this covers every block of b
orbits up to symmetry.

Usage: python3 cayley_blocks.py alpha beta j b timeout_s [limit]
  e.g. Sym(4) family, depth 2:  1,0,2,3 1,2,3,0 2 3 120
Set DEEP_BIN to the compiled fpbs-overfold-exact-c-2026-09-17/deep.c.
"""
import os
import sys
import time
from collections import Counter
from itertools import combinations
E = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
sys.path.insert(0, E + '/fpbs-overfold-embedded-orbits-2026-09-17')
sys.path.insert(0, E + '/fpbs-overfold-exact-c-2026-09-17')
sys.path.insert(0, E + '/fpbs-overfold-relative-rank-2026-09-17')
from ecensus import cayley_level
from elevels import comp_defects, e_defect
import blocks
al = tuple(int(x) for x in sys.argv[1].split(','))
be = tuple(int(x) for x in sys.argv[2].split(','))
j = int(sys.argv[3]); b = int(sys.argv[4]); to = int(sys.argv[5])
lim = int(sys.argv[6]) if len(sys.argv) > 6 else 10 ** 9
PA, PB = cayley_level(al, be, 100000)
print('n', len(PA), 'E defect', e_defect(PA, PB, j), 'orbit sizes', Counter(comp_defects(PA, PB, j)[0]))
sys.stdout.flush()
t0 = time.time()
Gj, G, m, kj, orb = blocks.setup(PA, PB, j)
print('setup', G.V, 'vertices', kj, 'orbits', round(time.time() - t0, 1), 's'); sys.stdout.flush()
O0 = orb[0]
inst, _, _, _ = blocks.instance(G, m, orb, [O0])
law0, _ = blocks.run(inst, 40, True, to)
print('law of one orbit', law0); sys.stdout.flush()
stat = Counter()
cnt = 0
for rest in combinations([O for O in range(kj) if O != O0], b - 1):
    W = (O0,) + rest
    inst, nv, ns, ncross = blocks.instance(G, m, orb, W)
    lw = law0 * b
    d, st = blocks.run(inst, lw - 1, False, to)
    if d is not None:
        v = 'COUNTEREXAMPLE' if d < lw else 'ok'
    elif st == 'complete':
        v = 'deepc=law'
    else:
        v = 'deepc>=%d (timeout)' % (st + 1)
    stat[v] += 1
    print('  block', W, 'V', nv, 'seeds', ns, 'cross', ncross, v); sys.stdout.flush()
    cnt += 1
    if cnt >= lim:
        break
print('SUMMARY', dict(stat))
