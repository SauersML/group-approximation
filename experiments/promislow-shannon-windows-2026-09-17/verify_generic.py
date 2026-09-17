#!/usr/bin/env python3
"""Exact rational verification of a minimal-window Shannon fake over any group class.

Same checks as ../shannon-window-certificates-2026-09-17/verify_fake.py, for a group object G
(with .one, .mul, .inv): take a vertex solution (dual simplex), rationalise it, rebuild h on all
2^n subsets WITHOUT variable merging and verify exactly with fractions.Fraction:
  (P) h(empty) = 0, every elemental Shannon inequality;
  (I) h(x_g) = 1 for g in X, h(x_X) = |X|;
  (D) h(y_g u x_{gE}) = h(x_{gE}) for g in F;
  (T) h(S) = h(tS) for every t = p q^-1 (p, q ground sites) and S with S, tS in the ground set;
then print Phi = h(y_f0) + h(x_1 u y_F) - h(y_F).  Exit code 0 iff all checks pass and Phi < 1.

usage: verify_generic.py GROUP 'E' 'F'   with GROUP in k2, dinf, zz2, cyc7, cyc5 and elements as Python literals
  e.g. verify_generic.py k2 "[(0,0),(1,0),(0,1),(1,1)]" "[(0,0),(1,1),(0,1)]"
"""
import sys, os, ast
from fractions import Fraction as Fr
from itertools import combinations
from scipy.optimize import linprog
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'shannon-window-certificates-2026-09-17'))
from shannon_lp import build, constraints, objective, show
from torsion2_scan import group
from random_scan import Cyc


def lp_vertex(d):
    A_ub, b_ub, A_eq, b_eq, _ = constraints(d)
    c = objective(d)
    return linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=(0, None), method='highs-ds')


def verify(G, E, F, maxden=2000):
    d = build(G, E, F)
    res = lp_vertex(d)
    assert res.status == 0, res.message
    val = [Fr(v).limit_denominator(maxden) for v in res.x]
    items, idx, n = d['items'], d['idx'], d['n']
    N = 1 << n
    h = [val[d['col'][m]] for m in range(N)]
    bad = []
    if h[0] != 0:
        bad.append('h(empty)')
    nel = 0
    for i in range(n):
        nel += 1
        if h[N - 1] < h[(N - 1) ^ (1 << i)]:
            bad.append('mono %d' % i)
    for i, j in combinations(range(n), 2):
        for K in range(N):
            if K >> i & 1 or K >> j & 1:
                continue
            nel += 1
            if h[K | 1 << i] + h[K | 1 << j] < h[K | 1 << i | 1 << j] + h[K]:
                bad.append('sub %d %d %d' % (i, j, K))
    def m(its):
        r = 0
        for it in its:
            r |= 1 << idx[it]
        return r
    for g in d['X']:
        if h[m([('x', g)])] != 1:
            bad.append('unit x')
    if h[m([('x', g) for g in d['X']])] != len(d['X']):
        bad.append('independence')
    for g in d['Y']:
        w = [('x', G.mul(g, e)) for e in E]
        if h[m(w + [('y', g)])] != h[m(w)]:
            bad.append('function y')
    sites = list(dict.fromkeys(d['X'] + d['Y']))
    trans = {G.mul(p, G.inv(q)) for p in sites for q in sites}
    ntr = 0
    for t in trans:
        for S in range(1, N):
            its = [items[i] for i in range(n) if S >> i & 1]
            im = [(k, G.mul(t, g)) for (k, g) in its]
            if all(it in idx for it in im):
                ntr += 1
                if h[S] != h[m(im)]:
                    bad.append('translation')
    yF = [('y', f) for f in d['F']]
    phi = h[m([('y', d['F'][0])])] + h[m([('x', G.one)] + yF)] - h[m(yF)]
    ok = not bad
    print('E=%s F=%s ground set %d: %d elemental inequalities, %d translation equalities checked: %s'
          % (show(G, E), show(G, F), n, nel, ntr, 'ALL EXACT' if ok else 'FAILED (%d violations, e.g. %s)' % (len(bad), bad[:3])))
    print('  exact Phi of rationalised polymatroid = %s (LP float %.9f)' % (phi, res.fun))
    return ok and phi < 1


if __name__ == '__main__':
    name = sys.argv[1]
    if name.startswith('cyc'):
        G = Cyc(int(name[3:]))
    else:
        G, _ = group(name)
    E = ast.literal_eval(sys.argv[2]); F = ast.literal_eval(sys.argv[3])
    if len(sys.argv) > 4:
        ok = verify(G, E, F, int(sys.argv[4]))
    else:
        ok = verify(G, E, F)
    sys.exit(0 if ok else 1)
