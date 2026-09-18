"""Transitive BFS-standard census: smallest index of a subgroup of
Delta_(n,n+1) containing C1,(n+1) and excluding om.  u_(n+1) is set trivial
(it only commutes with the other u's, so this loses no overgroup that
matters for the existence question of om moving the base point: any action
restricts to one where u_(n+1) acts trivially?  NO -- so we run both)."""
import sys, time
import overgroup_sat as O
from pysat.solvers import Solver

n, kmin, kmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
top_trivial = len(sys.argv) > 4 and sys.argv[4] == 'top1'
m = n + 1
for k in range(kmin, kmax + 1):
    t0 = time.time()
    E, G = O.build(n, m, k)
    gens = [G['w']] + G['u'] + [G['om']]
    O.standardize(E, gens)
    if top_trivial:
        for i in range(k):
            E.cl.append([G['u'][m][i][i]])
    with Solver(name='cadical153', bootstrap_with=E.cl) as S:
        ok = S.solve()
        line = f'n={n} k={k} top_trivial={top_trivial} SAT={ok} t={time.time()-t0:.1f}s'
        if ok:
            M = S.get_model()
            for name in ['w', 'om']:
                line += f' {name}=' + str(O.decode(G[name], k, M))
            line += ' u=' + str([O.decode(x, k, M) for x in G['u']])
        print(line, flush=True)
