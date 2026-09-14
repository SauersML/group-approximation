#!/usr/bin/env python3
"""Gardam's complex unit is a unit of a twisted integral group ring Z^c[P].

Lane ideas-kaplansky-atiyah-2, 2026-09-14. Exact integer arithmetic only.

Gardam (arXiv:2312.05240, proof of Theorem A) gives alpha, beta in R[P],
R = Z[s,t]/(s^4+1, t^4+1), with alpha*beta = 1 and every coefficient a signed
monomial +-s^i t^j. The term lists below are copied from
research/artifacts/gardam-support-pair-gsp.py (which checks them against
zenodo 14008425). This script checks:

 (1) the class map g -> (i mod 4, j mod 4) on supp(alpha) and supp(beta) is
     the restriction of the homomorphism rho: P -> (Z/4)^2 with
     rho(a) = (1,0), rho(b) = (0,1); P^ab = (Z/4)^2, so rho is well defined;
 (2) with representatives it(g), jt(g) in {0,1,2,3} of rho(g), the cocycle
     c(g,h) = (-1)^([it(g)+it(h) >= 4] + [jt(g)+jt(h) >= 4]) defines Z^c[P],
     and abar = sum eps_g g, bbar = sum eta_h h (signs from alpha, beta)
     satisfy abar * bbar = bbar * abar = 1 in Z^c[P];
 (3) psi = rho_1 + rho_2 takes the value 1 on a, so psi: P -> Z/4 is onto.
"""
from collections import defaultdict

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
assert mul(a, A) == E and mul(b, B) == E
def word(letters):
    r = E
    for g in letters:
        r = mul(r, g)
    return r
assert word([A, b, b, a, b, b]) == E and word([B, a, a, b, a, a]) == E

# letters: group element and rho value in (Z/4)^2
L = {'x': (word([a, a]), (2, 0)), 'y': (word([b, b]), (0, 2)), 'z': (word([a, b, a, b]), (2, 2))}
L['X'] = (inv(L['x'][0]), (2, 0)); L['Y'] = (inv(L['y'][0]), (0, 2)); L['Z'] = (inv(L['z'][0]), (2, 2))
COS = {'1': (E, (0, 0)), 'a': (a, (1, 0)), 'b': (b, (0, 1)), 'ab': (mul(a, b), (1, 1))}

def element(ws, coset):
    g, r = E, (0, 0)
    for ch in ws:
        h, v = L[ch]
        g, r = mul(g, h), ((r[0] + v[0]) % 4, (r[1] + v[1]) % 4)
    h, v = COS[coset]
    return mul(g, h), ((r[0] + v[0]) % 4, (r[1] + v[1]) % 4)

SHIFT = {'1': (0, 0), 'a': (1, 0), 'b': (0, 1), 'ab': (1, 1)}
def assemble(parts):
    """parts: coset -> list of (sign, i, j, word); coefficient s^i t^j times coset shift."""
    out, rho = {}, {}
    for coset, terms in parts.items():
        for sign, i, j, ws in terms:
            g, r = element(ws, coset)
            ii, jj = i + SHIFT[coset][0], j + SHIFT[coset][1]
            sg = sign * (-1) ** (ii // 4 + jj // 4)
            ii, jj = ii % 4, jj % 4
            assert g not in out
            out[g] = (sg, ii, jj)
            rho[g] = r
    return out, rho

alpha, rho_a = assemble({
    '1': [(1, 0, 0, ''), (1, 0, 2, 'xZ'), (-1, 0, 2, 'XZ'), (-1, 2, 0, 'yZ'), (1, 2, 0, 'YZ')],
    'a': [(-1, 2, 0, 'X'), (1, 0, 0, ''), (-1, 0, 0, 'XYz'), (1, 2, 0, 'yz')],
    'b': [(1, 0, 0, 'XYz'), (-1, 0, 2, 'xz'), (1, 0, 2, 'Yzz'), (-1, 0, 0, 'zz')],
    'ab': [(-1, 0, 2, 'XZ'), (-1, 2, 0, 'yZ'), (1, 2, 2, 'Z'), (1, 0, 0, 'XyZ'),
           (1, 2, 0, 'XZZ'), (1, 0, 2, 'yZZ'), (-1, 0, 0, 'ZZ'), (-1, 2, 2, 'XyZZ')]})
beta, rho_b = assemble({
    '1': [(1, 0, 0, ''), (1, 0, 2, 'Xz'), (-1, 0, 2, 'xz'), (1, 2, 0, 'yz'), (-1, 2, 0, 'Yz')],
    'a': [(-1, 0, 0, ''), (1, 2, 0, 'X'), (-1, 2, 0, 'yz'), (1, 0, 0, 'XYz')],
    'b': [(-1, 0, 0, 'XYz'), (1, 0, 2, 'xz'), (-1, 0, 2, 'Yzz'), (1, 0, 0, 'zz')],
    'ab': [(1, 2, 2, 'Xy'), (1, 0, 0, ''), (-1, 0, 2, 'y'), (-1, 2, 0, 'X'), (-1, 0, 0, 'Xyz'),
           (-1, 2, 2, 'z'), (1, 2, 0, 'yz'), (1, 0, 2, 'Xz')]})
print("|supp alpha| =", len(alpha), " |supp beta| =", len(beta))

# (1) coefficient class equals rho(g) (degree-0 homogeneity), for alpha and beta
cls_ok = all((ii, jj) == rho_a[g] for g, (sg, ii, jj) in alpha.items()) and \
         all((ii, jj) == rho_b[g] for g, (sg, ii, jj) in beta.items())
print("(1) every coefficient class equals rho(g):", cls_ok)

# rho is a function on P: consistency on elements reached twice (across alpha, beta)
common = set(rho_a) & set(rho_b)
print("    rho agrees on", len(common), "common support elements:", all(rho_a[g] == rho_b[g] for g in common))

# (2) product in the twisted ring Z^c[P]
def cocycle(r, s_):
    return (-1) ** ((r[0] + s_[0] >= 4) + (r[1] + s_[1] >= 4))
def tmul(U, RU, V, RV):
    out = defaultdict(int)
    for g, (sg, ii, jj) in U.items():
        for h, (sh, kk, ll) in V.items():
            out[mul(g, h)] += sg * sh * cocycle(RU[g], RV[h])
    return {k: v for k, v in out.items() if v}
ab_ = tmul(alpha, rho_a, beta, rho_b)
ba_ = tmul(beta, rho_b, alpha, rho_a)
print("(2) abar*bbar == 1 in Z^c[P]:", ab_ == {E: 1}, "  bbar*abar == 1:", ba_ == {E: 1})
print("    abar coefficients are +-1 with 21 terms:", len(alpha) == 21)

# (2') same product in R[P] (untwisted, with the monomial coefficients) as a control
def rmono_mul(p, q):
    sg, i, j = p; sh, k, l = q
    ii, jj = i + k, j + l
    return sg * sh * (-1) ** (ii // 4 + jj // 4), ii % 4, jj % 4
out = defaultdict(lambda: defaultdict(int))
for g, p in alpha.items():
    for h, q in beta.items():
        sgn, ii, jj = rmono_mul(p, q)
        out[mul(g, h)][(ii, jj)] += sgn
out = {k: {m: v for m, v in d.items() if v} for k, d in out.items()}
out = {k: d for k, d in out.items() if d}
print("    control alpha*beta == 1 in R[P]:", out == {E: {(0, 0): 1}})

# (3) psi = rho_1 + rho_2 is onto Z/4 (value 1 at a)
print("(3) psi(a) = (rho_1+rho_2)(a) =", (COS['a'][1][0] + COS['a'][1][1]) % 4)
