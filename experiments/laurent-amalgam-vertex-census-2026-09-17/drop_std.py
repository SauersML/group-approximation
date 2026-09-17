"""Relator-drop diagnostics for Delta_(2,3) with BFS-standard transitive
actions: smallest index <= kmax of an overgroup of C1,3 excluding om."""
import sys
import overgroup_sat as O
from pysat.solvers import Solver

kmax = int(sys.argv[1])
cases = [(), ('tri1',), ('tri2',), (('rot', 1),), (('com', 0, 2),),
         (('com', 0, 3),), (('ucom', 0, 1),), (('ucom', 0, 2),),
         (('ucom', 1, 2),), (('ucom', 0, 3),), (('ucom', 1, 3),),
         (('ucom', 2, 3),)]
for drop in cases:
    found = None
    for k in range(2, kmax + 1):
        E, G = O.build(2, 3, k, drop=drop)
        O.standardize(E, [G['w']] + G['u'] + [G['om']])
        with Solver(name='cadical153', bootstrap_with=E.cl) as S:
            if S.solve():
                found = k
                break
    print('drop', drop, 'smallest index', found, flush=True)
