#!/usr/bin/env python3
"""Definite dihedral shadows of R[P] on the three lines {x=y=-1}, {y=z=-1}, {x=z=-1}.

On each line the quotient of R[P] is D(R) = R[t^+-1]<u | u^2 = -1, u t = t^-1 u>, elements l0 + l1 u.
  line C (x=y=-1): t=ab, u=a;  phi(x^i y^j z^k c) = (-1)^(i+j) t^(2k) phi(c), phi(1,a,b,ab) = 1, u, -t^-1 u, t
  line A (y=z=-1): t=a,  u=b;  phi(...) = (-1)^(j+k) t^(2i) phi(c),       phi(1,a,b,ab) = 1, t, u, t u
  line B (x=z=-1): t=b,  u=a;  phi(...) = (-1)^(i+k) t^(2j) phi(c),       phi(1,a,b,ab) = 1, u, t, t^-1 u
Checks: phi is multiplicative on the P-model (relators, random products); Gardam's complex unit
(s=t=zeta_8) and its inverse multiply to 1 in D(Z[zeta_8]); prints the shadows and N = l0 l0bar + l1 l1bar.
"""
import sys, itertools, random, importlib.util
sys.argv = ['gsp']
spec = importlib.util.spec_from_file_location('gsp', sys.path[0] + '/gardam-support-pair-gsp.py')
G = importlib.util.module_from_spec(spec); spec.loader.exec_module(G)

def zadd(u, v): return tuple(u[i] + v[i] for i in range(4))
def zmul(u, v):
    out = [0] * 8
    for i in range(4):
        for j in range(4):
            out[i + j] += u[i] * v[j]
    return tuple(out[i] - out[i + 4] for i in range(4))
ZERO, ONE = (0, 0, 0, 0), (1, 0, 0, 0)
def zsc(n, u): return tuple(n * c for c in u)
def zpow_s(k):
    k %= 8
    return tuple(1 if i == k else 0 for i in range(4)) if k < 4 else tuple(-1 if i == k - 4 else 0 for i in range(4))
def coef_to_z(c):
    out = ZERO
    for (i, j), m in c.items():
        out = zadd(out, zsc(m, zpow_s(i + j)))
    return out
# Laurent polys in t over Z[zeta8]: dict exp -> 4-tuple
def ladd(p, q):
    out = dict(p)
    for k, v in q.items():
        out[k] = zadd(out.get(k, ZERO), v)
    return {k: v for k, v in out.items() if v != ZERO}
def lmul(p, q):
    out = {}
    for k1, v1 in p.items():
        for k2, v2 in q.items():
            out[k1 + k2] = zadd(out.get(k1 + k2, ZERO), zmul(v1, v2))
    return {k: v for k, v in out.items() if v != ZERO}
def lbar(p): return {-k: v for k, v in p.items()}
def lneg(p): return {k: zsc(-1, v) for k, v in p.items()}
def dmul(X, Y):
    (l0, l1), (m0, m1) = X, Y
    return (ladd(lmul(l0, m0), lneg(lmul(l1, lbar(m1)))), ladd(lmul(l0, m1), lmul(l1, lbar(m0))))
def dadd(X, Y): return (ladd(X[0], Y[0]), ladd(X[1], Y[1]))
DONE_ONE = ({0: ONE}, {})

SIGNS = {'e': (1, 1, 1), 'A': (1, -1, -1), 'B': (-1, 1, -1), 'C': (-1, -1, 1)}
REP = {'e': G.E, 'A': G.a, 'B': G.b, 'C': G.w(G.a, G.b)}
def decompose(g):
    sg = (g[0][0], g[1][1], g[2][2])
    c = next(k for k, v in SIGNS.items() if v == sg)
    tau = tuple(g[i][3] - REP[c][i][3] for i in range(3))
    assert G.mul(((1,0,0,tau[0]),(0,1,0,tau[1]),(0,0,1,tau[2]),(0,0,0,1)), REP[c]) == g
    return (tau[0] // 2, tau[1] // 2, -tau[2] // 2), c
def sgn(n): return -1 if n % 2 else 1

def mono(e, coef=ONE): return {e: coef}
def phi_elem(line, g, coef=ONE):
    (i, j, k), c = decompose(g)
    if line == 'C':
        sc, sh = sgn(i + j), 2 * k
        table = {'e': (mono(0), {}), 'A': ({}, mono(0)), 'B': ({}, mono(-1, zsc(-1, ONE))), 'C': (mono(1), {})}
    elif line == 'A':
        sc, sh = sgn(j + k), 2 * i
        table = {'e': (mono(0), {}), 'A': (mono(1), {}), 'B': ({}, mono(0)), 'C': ({}, mono(1))}
    else:
        sc, sh = sgn(i + k), 2 * j
        table = {'e': (mono(0), {}), 'A': ({}, mono(0)), 'B': (mono(1), {}), 'C': ({}, mono(-1))}
    l0, l1 = table[c]
    pre = {sh: zsc(sc, coef)}
    return (lmul(pre, l0), lmul(pre, l1))
def phi(line, U):
    out = ({}, {})
    for g, c in U.items():
        out = dadd(out, phi_elem(line, g, coef_to_z(c)))
    return out

random.seed(1)
gens = [G.a, G.b, G.A, G.B]
for line in 'CAB':
    # multiplicativity on random words
    for _ in range(300):
        g = G.E; h = G.E
        for _ in range(random.randint(0, 7)): g = G.mul(g, random.choice(gens))
        for _ in range(random.randint(0, 7)): h = G.mul(h, random.choice(gens))
        assert dmul(phi_elem(line, g), phi_elem(line, h)) == phi_elem(line, G.mul(g, h)), line
    pa, pb = phi(line, G.alpha), phi(line, G.beta)
    ok = dmul(pa, pb) == DONE_ONE and dmul(pb, pa) == DONE_ONE
    N = ladd(lmul(pa[0], lbar(pa[0])), lmul(pa[1], lbar(pa[1])))
    nonzero_terms = sum(len(pa[0]) + len(pa[1]) for _ in [0])
    print("line", line, "| phi(alpha)phi(beta)=1:", ok, "| terms in shadow:", nonzero_terms)
    print("   l0 =", dict(sorted(pa[0].items())))
    print("   l1 =", dict(sorted(pa[1].items())))
    print("   N = l0 l0bar + l1 l1bar =", dict(sorted(N.items())))
# trivial units: shadows are signed monomials
for line in 'CAB':
    for g in G.S + G.T:
        X = phi_elem(line, g)
        assert len(X[0]) + len(X[1]) == 1 and list((X[0] or X[1]).values())[0] in (ONE, zsc(-1, ONE))
print("trivial units of S and T have one-term shadows on all three lines: ok")
print("DONE")
