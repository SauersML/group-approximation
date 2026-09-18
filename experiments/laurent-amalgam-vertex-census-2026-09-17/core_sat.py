"""Core relaxation of Delta_(2,3).

Group P = <w,u,a,om | involutions, (w u)^3, (om a)^3, [a, s a s^-1]>,
s = om w.  Base point x0 fixed by w,u,a and u fixing om x0 (this is
u_2 = w om u om w fixing x0).  Question: must om fix x0 in every finite
action?  Search transitive BFS-standard actions on k points."""
import sys, time
import overgroup_sat as O
from pysat.solvers import Solver

kmin, kmax = int(sys.argv[1]), int(sys.argv[2])
variant = sys.argv[3] if len(sys.argv) > 3 else 'core'
for k in range(kmin, kmax + 1):
    t0 = time.time()
    E = O.Enc(k)
    w, u, a, om = (E.perm(True) for _ in range(4))
    E.order3(E.compose(w, u))
    E.order3(E.compose(om, a))
    s = E.compose(w, om)          # apply w then om: s = om w
    sinv = E.compose(om, w)
    sas = E.word([sinv, a, s])    # apply s^-1, a, s  => s a s^-1
    if variant != 'noC':
        E.commute(a, sas)
    u1 = E.word([w, a, w])
    u2 = E.word([w, om, u, om, w])
    V = {'01': (u, u1), '02': (u, u2), '12': (u1, u2)}
    for key, (p, q) in V.items():
        if key in variant:
            E.commute(p, q)
    for g in (w, u, a):
        E.cl.append([g[0][0]])
    uu = E.word([om, u, om])      # om u om fixes x0 <=> u fixes om x0
    E.cl.append([uu[0][0]])
    E.cl.append([-om[0][0]])
    O.standardize(E, [w, u, a, om])
    with Solver(name='cadical153', bootstrap_with=E.cl) as S:
        ok = S.solve()
        line = f'core variant={variant} k={k} SAT={ok} t={time.time()-t0:.1f}s'
        if ok:
            M = S.get_model()
            line += ' ' + str([O.decode(x, k, M) for x in (w, u, a, om)])
        print(line, flush=True)
        if ok:
            break
