"""Sanity check: the SL_2(F_4) action on P^1(F_4), t -> a root of t^2+t+1,
satisfies the Delta_(2,3) relators as encoded in overgroup_sat.build."""
import overgroup_sat as O
from pysat.solvers import Solver


def mul(a, b):
    r = 0
    for i in range(2):
        if (b >> i) & 1:
            r ^= a << i
    if r & 4:
        r ^= 0b111
    return r


def inv(a):
    return [x for x in range(1, 4) if mul(a, x) == 1][0]


pts = [(1, x) for x in range(4)] + [(0, 1)]


def norm(v):
    a, b = v
    if a == 0:
        return (0, 1)
    return (1, mul(inv(a), b))


def act(M):
    (a, b), (c, d) = M
    return [pts.index(norm((mul(a, p) ^ mul(b, q), mul(c, p) ^ mul(d, q))))
            for (p, q) in pts]


t = 2
tinv, t2 = inv(t), mul(t, t)
tp = [1, t, t2, mul(t2, t)]
perms = dict(w=act(((0, 1), (1, 0))), om=act(((0, tinv), (t, 0))),
             u=[act(((1, x), (0, 1))) for x in tp])
k = 5
for bad in [False, True]:
    E, G = O.build(2, 3, k)
    E.cl = [c for c in E.cl if len(c) > 1]

    def fix(P, perm):
        for i in range(k):
            E.cl.append([P[i][perm[i]]])
    fix(G['w'], perms['w'])
    om = perms['om'] if not bad else perms['w']
    fix(G['om'], om)
    for x, p in zip(G['u'], perms['u']):
        fix(x, p)
    with Solver(name='cadical153', bootstrap_with=E.cl) as S:
        print('om=w (should fail)' if bad else 'F4 model', 'SAT =', S.solve())
