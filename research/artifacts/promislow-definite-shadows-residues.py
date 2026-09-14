#!/usr/bin/env python3
"""Definite-line shadows of Gardam's unit of F_2[P] and of Murray's units of F_d[P] (Theorem 3).

Lines: C = {x=y=-1} (t=ab, u=a), A = {y=z=-1} (t=a, u=b), B = {x=z=-1} (t=b, u=a),
D(F) = F[t^+-1]<u | u^2=-1, u t = t^-1 u>, norm N(l0 + l1 u) = l0 l0bar + l1 l1bar.
"""
import sys, itertools, importlib.util
sys.argv = ['gsp']
spec = importlib.util.spec_from_file_location('gsp', sys.path[0] + '/gardam-support-pair-gsp.py')
G = importlib.util.module_from_spec(spec); spec.loader.exec_module(G)

def lred(A, P): return {k: v % P for k, v in A.items() if v % P}
def ladd(A, B, P):
    out = dict(A)
    for k, v in B.items(): out[k] = out.get(k, 0) + v
    return lred(out, P)
def lmul(A, B, P):
    out = {}
    for k1, v1 in A.items():
        for k2, v2 in B.items(): out[k1 + k2] = out.get(k1 + k2, 0) + v1 * v2
    return lred(out, P)
def lbar(A): return {-k: v for k, v in A.items()}
def lshift(A, e, c=1): return {k + e: c * v for k, v in A.items()}
def dmul(X, Y, P):
    (l0, l1), (m0, m1) = X, Y
    return (ladd(lmul(l0, m0, P), lshift(lmul(l1, lbar(m1), P), 0, -1), P), ladd(lmul(l0, m1, P), lmul(l1, lbar(m0), P), P))
def dnorm(X, P): return ladd(lmul(X[0], lbar(X[0]), P), lmul(X[1], lbar(X[1]), P), P)
def monomial_shadow(X, P):
    terms = len(X[0]) + len(X[1])
    return terms == 1 and list((X[0] or X[1]).values())[0] in (1, P - 1)

SIGNS = {'e': (1, 1, 1), 'A': (1, -1, -1), 'B': (-1, 1, -1), 'C': (-1, -1, 1)}
REP = {'e': G.E, 'A': G.a, 'B': G.b, 'C': G.w(G.a, G.b)}
def decompose(g):
    sg = (g[0][0], g[1][1], g[2][2])
    c = next(k for k, v in SIGNS.items() if v == sg)
    tau = tuple(g[i][3] - REP[c][i][3] for i in range(3))
    assert G.mul(((1,0,0,tau[0]),(0,1,0,tau[1]),(0,0,1,tau[2]),(0,0,0,1)), REP[c]) == g
    return (tau[0] // 2, tau[1] // 2, -tau[2] // 2), c

# ---- shadow of p + q a + r b + s ab, with p,q,r,s Laurent in x,y,z: dict (i,j,k)->int ----
def spec_line(Pxyz, line):
    out = {}
    for (i, j, k), v in Pxyz.items():
        if line == 'C': sc, e = (-1) ** ((i + j) % 2), 2 * k
        elif line == 'A': sc, e = (-1) ** ((j + k) % 2), 2 * i
        else: sc, e = (-1) ** ((i + k) % 2), 2 * j
        out[e] = out.get(e, 0) + sc * v
    return out
def shadow(pqrs, line, P):
    p, q, r, s = [spec_line(f, line) for f in pqrs]
    if line == 'C':   # 1, a, b, ab -> 1, u, -t^-1 u, t
        l0 = ladd(p, lshift(s, 1), P); l1 = ladd(q, lshift(r, -1, -1), P)
    elif line == 'A': # 1, a, b, ab -> 1, t, u, t u
        l0 = ladd(p, lshift(q, 1), P); l1 = ladd(r, lshift(s, 1), P)
    else:             # 1, a, b, ab -> 1, u, t, t^-1 u
        l0 = ladd(p, lshift(r, 1), P); l1 = ladd(q, lshift(s, -1), P)
    return (l0, l1)
def group_ring_to_pqrs(U, coef):
    pqrs = [{}, {}, {}, {}]
    idx = {'e': 0, 'A': 1, 'B': 2, 'C': 3}
    for g, c in U.items():
        m, cc = decompose(g)
        d = pqrs[idx[cc]]; d[m] = d.get(m, 0) + coef(c)
    return pqrs
def report(name, pqrs, P, inv=None):
    killed = []
    for line in 'CAB':
        X = shadow(pqrs, line, P)
        N = dnorm(X, P)
        extra = ''
        if inv is not None:
            Y = shadow(inv, line, P)
            extra = ' | shadow(u)shadow(u^-1)=1: %s' % (dmul(X, Y, P) == ({0: 1}, {}))
        mono = monomial_shadow(X, P)
        if not mono: killed.append(line)
        print('  %s line %s: l0=%s l1=%s | N=%s | signed monomial: %s%s' % (name, line, dict(sorted(X[0].items())), dict(sorted(X[1].items())), N, mono, extra))
    print('  %s -> non-monomial shadow on lines %s' % (name, killed or 'NONE'))
    return killed

# ---- Gardam's unit of F_2[P]: reduction of the complex unit (every coefficient +-s^i t^j = 1 mod 2) ----
one_coef = lambda c: sum(c.values())
print('Gardam F_2 unit (support 21):')
kg = report('gardam', group_ring_to_pqrs(G.alpha, one_coef), 2, group_ring_to_pqrs(G.beta, one_coef))

# ---- Murray's Theorem 3 units of F_d[P] ----
def lp_add(*Ps):
    out = {}
    for P_ in Ps:
        for k, v in P_.items(): out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v}
def lp_mul(*Ps):
    out = {(0, 0, 0): 1}
    for P_ in Ps:
        new = {}
        for k1, v1 in out.items():
            for k2, v2 in P_.items():
                k = (k1[0] + k2[0], k1[1] + k2[1], k1[2] + k2[2]); new[k] = new.get(k, 0) + v1 * v2
        out = {k: v for k, v in new.items() if v}
    return out
def mono(i, j, k, c=1): return {(i, j, k): c}
X_, Xi, Y_, Yi = mono(1,0,0), mono(-1,0,0), mono(0,1,0), mono(0,-1,0)
ONE = mono(0, 0, 0)
def zp(e, c=1): return mono(0, 0, e, c)
for d in (3, 5, 7):
    for t_, w_ in itertools.product((-1, 0, 1, 2), (0, 1)):
        h = ONE
        for _ in range(d - 2): h = lp_mul(h, lp_add(ONE, zp(1 - 2 * t_, -1)))
        f1 = lp_mul(lp_add(zp(t_), zp(1 - t_)), h); f2 = lp_mul(zp(w_), h)
        f3 = lp_mul(zp(w_), lp_add(ONE, zp(2 * t_ - 1)), h); f4 = lp_mul(zp(w_ + t_), h)
        f5 = lp_mul(zp(w_), lp_add(zp(t_), zp(1 - t_)), h); f6 = h; f7 = zp(2 * t_ - 1)
        p = lp_mul(lp_add(ONE, X_), lp_add(ONE, Y_), f1)
        q = lp_add(lp_mul(lp_add(ONE, X_), lp_add(Xi, Yi), f2), lp_mul(lp_add(ONE, Yi), f3))
        r = lp_add(lp_mul(lp_add(ONE, Yi), lp_add(X_, Y_), f4), lp_mul(lp_add(ONE, X_), f5))
        s = lp_add(lp_mul(lp_add(X_, mono(0,0,0,4), Xi, Y_, Yi), f6), f7)
        print('Murray Theorem 3, d = %d, t = %d, w = %d:' % (d, t_, w_))
        report('murray', [p, q, r, s], d)
print('DONE')
