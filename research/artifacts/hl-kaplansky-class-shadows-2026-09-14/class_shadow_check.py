#!/usr/bin/env python3
"""Class sensitivity of the definite dihedral shadows of the Promislow group.

Lane hl-kaplansky-class-shadows, 2026-09-14. Exact integer arithmetic only.

P = <a, b | b^-1 a^2 b a^2 = 1, a^-1 b^2 a b^2 = 1> (affine model as in
research/artifacts/ideas-kaplansky-atiyah-2-2026-09-14/twisted_integral_unit_check.py).
D(Z) = Z[t^+-1]<u | u^2 = -1, u t = t^-1 u>; its unit group is {+-t^m, +-t^m u}.

 (1) Relator signs. In R[P], R = Z[s,t]/(s^4+1, t^4+1), the twisted ring of the
     class (e1, e2) is spanned by s^(e1 it(g)) t^(e2 jt(g)) g. With abar = s^e1 a,
     bbar = t^e2 b, the relator lifts r1~ = bbar^-1 abar^2 bbar abar^2 and
     r2~ = abar^-1 bbar^2 abar bbar^2 equal (-1)^e1 and (-1)^e2.
 (2) Hom(P, D(Z)^x) on the box |m| <= 3: exactly the families RR (images +-1),
     RF, FR, FF; every RF/FR/FF solution is e o (shadow A, B or C) for an
     endomorphism e: t -> eps1 t^m1, u -> eps2 t^k2 u of D(Z).
 (3) Rigidity: no h, k in D(Z)^x (|m| <= 4) with k h^2 k^-1 = -h^-2.
 (4) zeta_8 witnesses: in D(Z[zeta_8]) the assignment a -> zeta_8^e1 u,
     b -> -zeta_8^e2 t^-1 u satisfies the twisted relators with signs
     ((-1)^e1, (-1)^e2), and h = zeta_8 u solves k h^2 k^-1 = -h^-2 with k = 1.
 (5) The (+,+) line quotient Z[P/<x,y>] = Z[D_inf] has the nontrivial unit
     1 + n, n = (1 - a) b (1 + a), n^2 = 0.
"""
from itertools import product

# ---------- affine model of P ----------
def mul(A, B):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(4)) for j in range(4)) for i in range(4))

def inv(A):
    R = [[A[j][i] for j in range(3)] for i in range(3)]
    t = [A[i][3] for i in range(3)]
    nt = [-sum(R[i][k] * t[k] for k in range(3)) for i in range(3)]
    return tuple(tuple(R[i]) + (nt[i],) for i in range(3)) + ((0, 0, 0, 1),)

E = ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))
a = ((1, 0, 0, 1), (0, -1, 0, 1), (0, 0, -1, 0), (0, 0, 0, 1))
b = ((-1, 0, 0, 0), (0, 1, 0, 1), (0, 0, -1, 1), (0, 0, 0, 1))
A, B = inv(a), inv(b)
def word(ls):
    r = E
    for g in ls:
        r = mul(r, g)
    return r
assert word([B, a, a, b, a, a]) == E and word([A, b, b, a, b, b]) == E
x, y = word([a, a]), word([b, b])
assert word([a, b, a, b]) != E and x != y

# ---------- (1) twisted monomials (sign, i, j, M) with s^4 = t^4 = -1 ----------
def tmul(p, q):
    si, sj = p[1] + q[1], p[2] + q[2]
    return (p[0] * q[0] * (-1) ** (si // 4 + sj // 4), si % 4, sj % 4, mul(p[3], q[3]))

def tinv(p):
    return (p[0] * (-1) ** ((p[1] != 0) + (p[2] != 0)), (-p[1]) % 4, (-p[2]) % 4, inv(p[3]))

def tword(ls):
    r = (1, 0, 0, E)
    for g in ls:
        r = tmul(r, g)
    return r

print("(1) relator signs of the four twisted models")
kappa = {}
for e1, e2 in product((0, 1), repeat=2):
    ab_, bb_ = (1, e1, 0, a), (1, 0, e2, b)
    for p in (ab_, bb_):
        assert tmul(p, tinv(p)) == (1, 0, 0, E) == tmul(tinv(p), p)
    r1 = tword([tinv(bb_), ab_, ab_, bb_, ab_, ab_])
    r2 = tword([tinv(ab_), bb_, bb_, ab_, bb_, bb_])
    assert r1[1:] == (0, 0, E) and r2[1:] == (0, 0, E)
    kappa[(e1, e2)] = (r1[0], r2[0])
    assert kappa[(e1, e2)] == ((-1) ** e1, (-1) ** e2)
    print(f"   class (e1,e2)=({e1},{e2}): r1~ = {r1[0]:+d}, r2~ = {r2[0]:+d}")
assert len(set(kappa.values())) == 4

# ---------- D(Z)^x monomials (eps, m, e) = eps t^m u^e ----------
def dmul(p, q):
    return (p[0] * q[0] * (-1) ** (p[2] * q[2]), p[1] + (-1) ** p[2] * q[1], (p[2] + q[2]) % 2)

def dinv(p):
    return (p[0], -p[1], 0) if p[2] == 0 else (-p[0], p[1], 1)

ONE = (1, 0, 0)
def dword(ls):
    r = ONE
    for g in ls:
        r = dmul(r, g)
    return r

def dpow(p, n):
    r = ONE
    for _ in range(abs(n)):
        r = dmul(r, p if n > 0 else dinv(p))
    return r

def box(M):
    return [(eps, m, e) for eps in (1, -1) for m in range(-M, M + 1) for e in (0, 1)]

for p in box(3):
    assert dmul(p, dinv(p)) == ONE == dmul(dinv(p), p)
T, U = (1, 1, 0), (1, 0, 1)
assert dmul(U, U) == (-1, 0, 0) and dword([U, T, dinv(U)]) == dinv(T)

def relators_hold(ia, ib):
    return (dword([dinv(ib), ia, ia, ib, ia, ia]) == ONE and
            dword([dinv(ia), ib, ib, ia, ib, ib]) == ONE)

SHADOW = {'A': (T, U), 'B': (U, T), 'C': (U, (-1, -1, 1))}
def endo(img, e):  # e = (eps1, m1, eps2, k2): t -> eps1 t^m1, u -> eps2 t^k2 u
    t_img, u_img = (e[0], e[1], 0), (e[2], e[3], 1)
    return dmul((img[0], 0, 0), dmul(dpow(t_img, img[1]), dpow(u_img, img[2])))

print("(2) homomorphisms P -> D(Z)^x on the box |m| <= 3")
fam = {'RR': 0, 'RF': 0, 'FR': 0, 'FF': 0}
for ia, ib in product(box(3), repeat=2):
    if not relators_hold(ia, ib):
        continue
    key = ('R' if ia[2] == 0 else 'F') + ('R' if ib[2] == 0 else 'F')
    fam[key] += 1
    if key == 'RR':
        assert ia[1] == 0 and ib[1] == 0
        continue
    sh = {'RF': 'A', 'FR': 'B', 'FF': 'C'}[key]
    ok = any(endo(SHADOW[sh][0], e) == ia and endo(SHADOW[sh][1], e) == ib
             for e in product((1, -1), range(-7, 8), (1, -1), range(-7, 8)))
    assert ok, (ia, ib)
for key in ('RF', 'FR', 'FF'):
    assert fam[key] == 2 * 7 * 2 * 7
assert fam['RR'] == 4
print("   solutions per family:", fam, "- all RF/FR/FF are e o shadow; RR images are +-1")

print("(3) rigidity of D(Z)^x")
hits = [(h, k) for h, k in product(box(4), repeat=2)
        if dword([k, h, h, dinv(k)]) == dmul((-1, 0, 0), dinv(dmul(h, h)))]
assert hits == []
print("   no h, k with |m| <= 4 satisfy k h^2 k^-1 = -h^-2")

# ---------- (4) D(Z[zeta_8]) monomials (z, m, e) = zeta_8^z t^m u^e ----------
def zmul(p, q):
    return ((p[0] + q[0] + 4 * p[2] * q[2]) % 8, p[1] + (-1) ** p[2] * q[1], (p[2] + q[2]) % 2)

def zinv(p):
    return ((-p[0]) % 8, -p[1], 0) if p[2] == 0 else ((4 - p[0]) % 8, p[1], 1)

def zword(ls):
    r = (0, 0, 0)
    for g in ls:
        r = zmul(r, g)
    return r

print("(4) zeta_8 witnesses in D(Z[zeta_8])")
for e1, e2 in product((0, 1), repeat=2):
    ia, ib = (e1, 0, 1), ((e2 + 4) % 8, -1, 1)
    for p in (ia, ib):
        assert zmul(p, zinv(p)) == (0, 0, 0)
    r1 = zword([zinv(ib), ia, ia, ib, ia, ia])
    r2 = zword([zinv(ia), ib, ib, ia, ib, ib])
    assert r1 == (4 * e1, 0, 0) and r2 == (4 * e2, 0, 0)
    print(f"   class ({e1},{e2}): a -> zeta^{e1} u, b -> -zeta^{e2} t^-1 u gives r1~ = zeta^{r1[0]}, r2~ = zeta^{r2[0]}")
h = (1, 0, 1)
assert zmul(h, h) == zmul((4, 0, 0), zinv(zmul(h, h)))
print("   h = zeta_8 u: h^2 = -h^-2, so k = 1 solves k h^2 k^-1 = -h^-2")

# ---------- (5) bicyclic unit in Z[D_inf] ----------
def gmul(p, q):  # D_inf = Z x| C2 as (m, e)
    return (p[0] + (-1) ** p[1] * q[0], (p[1] + q[1]) % 2)

def rmul(X, Y):
    out = {}
    for g, c in X.items():
        for h_, d in Y.items():
            k = gmul(g, h_)
            out[k] = out.get(k, 0) + c * d
    return {k: v for k, v in out.items() if v}

ea, eb, e0 = (0, 1), (1, 1), (0, 0)
assert gmul(ea, ea) == e0 and gmul(eb, eb) == e0
n = rmul(rmul({e0: 1, ea: -1}, {eb: 1}), {e0: 1, ea: 1})
assert rmul(n, n) == {}
one_plus, one_minus = dict(n), {k: -v for k, v in n.items()}
one_plus[e0] = one_plus.get(e0, 0) + 1
one_minus[e0] = one_minus.get(e0, 0) + 1
assert rmul(one_plus, one_minus) == {e0: 1} == rmul(one_minus, one_plus)
print(f"(5) 1 + (1-a)b(1+a) is a unit of Z[D_inf] with support {len(one_plus)}")
print("DONE")
