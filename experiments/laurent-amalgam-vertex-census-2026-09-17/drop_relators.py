"""Which relator of Delta_(2,3) blocks small overgroups of C1,3 excluding om?"""
import sys
import overgroup_sat as O
from pysat.solvers import Solver

kmax = int(sys.argv[1])
cases = [(), (('rot', 1),), ('tri2',), (('com', 0, 2),), (('com', 0, 3),),
         (('com', 0, 2), ('com', 0, 3))]
for drop in cases:
    found = None
    for k in range(2, kmax + 1):
        E, G = O.build(2, 3, k, drop=drop)
        with Solver(name='cadical153', bootstrap_with=E.cl) as S:
            if S.solve():
                found = k
                break
    print('drop', drop, 'smallest index', found, flush=True)
