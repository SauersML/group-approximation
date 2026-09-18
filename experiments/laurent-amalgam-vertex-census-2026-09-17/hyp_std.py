"""Which base-point hypotheses force om to fix x0 in finite Delta_(2,3)-sets?
('free', 0) releases w, ('free', j+1) releases u_j."""
import sys
import overgroup_sat as O
from pysat.solvers import Solver

kmax = int(sys.argv[1])
cases = [(('free', 0),), (('free', 1),), (('free', 2),), (('free', 3),),
         (('free', 4),), (('free', 3), ('free', 4)), (('free', 2), ('free', 4))]
for drop in cases:
    found = None
    for k in range(2, kmax + 1):
        E, G = O.build(2, 3, k, drop=drop)
        O.standardize(E, [G['w']] + G['u'] + [G['om']])
        with Solver(name='cadical153', bootstrap_with=E.cl) as S:
            if S.solve():
                M = S.get_model()
                found = (k, [O.decode(x, k, M) for x in [G['w']] + G['u'] + [G['om']]])
                break
    print('released', drop, '->', found, flush=True)
