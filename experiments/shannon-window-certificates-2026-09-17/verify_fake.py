#!/usr/bin/env python3
"""Exact rational verification of minimal-window Shannon fakes.

For a configuration (E, F) inside a cyclic group Z/n, solve the minimal-window LP with the
dual simplex (vertex solution), rationalise every coordinate, and then verify EXACTLY, with
fractions.Fraction and without the variable merging used by the LP, that the resulting set
function h on the ground set {x_g : g in X} u {y_g : g in F} satisfies

  (P) all elemental Shannon inequalities (h(N) >= h(N - i); h(iK)+h(jK) >= h(ijK)+h(K)), h(empty)=0;
  (I) h(x_g) = 1 for g in X and h(x_X) = |X|;
  (D) h(y_g u x_{g+E}) = h(x_{g+E}) for g in F;
  (T) h(S) = h(t+S) for every translation t and every S with S, t+S inside the ground set;

and prints Phi = h(y_{f0}) + h(x_0 u y_F) - h(y_F). Elemental inequalities imply all Shannon
inequalities, so h is a polymatroid satisfying every constraint a genuine configuration satisfies.

A second LP with Y = Z/n (all codewords of the finite orbit) is solved to show the fake disappears.
usage: verify_fake.py n 'E' 'F'   e.g. verify_fake.py 3 0,1,2 0,1
"""
import sys
from fractions import Fraction as Fr
from itertools import combinations
from scipy.optimize import linprog
from random_scan import Cyc
from shannon_lp import build, constraints, objective, show


def lp_vertex(d):
    A_ub, b_ub, A_eq, b_eq, _ = constraints(d)
    c = objective(d)
    return linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=(0, None), method='highs-ds')


def verify(n, E, F, maxden=1000):
    G = Cyc(n)
    d = build(G, E, F)
    res = lp_vertex(d)
    assert res.status == 0, res.message
    val = [Fr(v).limit_denominator(maxden) for v in res.x]
    items, idx, N = d['items'], d['idx'], 1 << d['n']
    h = [val[d['col'][m]] for m in range(N)]
    nfull = N - 1
    ok = True
    def fail(msg):
        nonlocal ok
        ok = False
        print('FAIL', msg)
    # (P)
    if h[0] != 0:
        fail('h(empty)')
    nel = 0
    for i in range(d['n']):
        nel += 1
        if h[nfull] < h[nfull ^ (1 << i)]:
            fail('mono %d' % i)
    for i, j in combinations(range(d['n']), 2):
        for K in range(N):
            if K >> i & 1 or K >> j & 1:
                continue
            nel += 1
            if h[K | 1 << i] + h[K | 1 << j] < h[K | 1 << i | 1 << j] + h[K]:
                fail('sub %d %d %d' % (i, j, K))
    def m(its):
        r = 0
        for it in its:
            r |= 1 << idx[it]
        return r
    # (I)
    for g in d['X']:
        if h[m([('x', g)])] != 1:
            fail('h(x_%s)' % g)
    if h[m([('x', g) for g in d['X']])] != len(d['X']):
        fail('independence')
    # (D)
    for g in d['Y']:
        w = [('x', (g + e) % n) for e in E]
        if h[m(w + [('y', g)])] != h[m(w)]:
            fail('function y_%s' % g)
    # (T)
    ntr = 0
    for t in range(1, n):
        for S in range(N):
            its = [items[i] for i in range(d['n']) if S >> i & 1]
            im = [(k, (g + t) % n) for (k, g) in its]
            if all(it in idx for it in im):
                ntr += 1
                if h[S] != h[m(im)]:
                    fail('translation t=%d S=%s' % (t, its))
    yF = [('y', f) for f in d['F']]
    phi = h[m([('y', d['F'][0])])] + h[m([('x', 0)] + yF)] - h[m(yF)]
    print('Z/%d E=%s F=%s ground set size %d; checked %d elemental inequalities, %d translation equalities: %s'
          % (n, show(G, E), show(G, F), d['n'], nel, ntr, 'ALL EXACT' if ok else 'FAILED'))
    print('  exact Phi of rationalised polymatroid = %s (LP float %.9f)' % (phi, res.fun))
    return d, h, phi, ok


def table(d, h, names):
    rows = []
    for S in range(1, 1 << d['n']):
        its = [d['items'][i] for i in range(d['n']) if S >> i & 1]
        rows.append((len(its), ' '.join('%s%s' % it for it in its), h[S]))
    for k, s, v in sorted(rows):
        if names is None or s in names:
            print('  h(%s) = %s' % (s, v))


if __name__ == '__main__':
    n = int(sys.argv[1])
    E = [int(v) for v in sys.argv[2].split(',')]
    F = [int(v) for v in sys.argv[3].split(',')]
    d, h, phi, ok = verify(n, E, F)
    if d['n'] <= 6:
        table(d, h, None)
    # closing the orbit: all codewords of Z/n
    G = Cyc(n)
    d2 = build(G, E, F, X=list(range(n)), Y=list(dict.fromkeys(F + [g for g in range(n) if g not in F])))
    r2 = lp_vertex(d2)
    print('  LP with Y = Z/%d (closed orbit, ground set %d): %.9f' % (n, d2['n'], r2.fun))
    sys.exit(0 if ok and phi < 1 else 1)
