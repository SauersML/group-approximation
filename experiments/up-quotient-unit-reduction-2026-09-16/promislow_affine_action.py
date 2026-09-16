"""Exact check, in the affine model of the Promislow group P, of the facts
used in Remark 4.3 of research/artifacts/up-quotient-unit-reduction-2026-09-16.md.

P = < a, b | b^-1 a^2 b = a^-2,  a^-1 b^2 a = b^-2 >, modelled by
a(v) = diag(1,-1,-1) v + (1/2, 1/2, 0),  b(v) = diag(-1,1,-1) v + (0, 1/2, 1/2).
Checks: both relators hold; x = a^2, y = b^2, z = (ab)^2 are translations by
+-e1, +-e2, +-e3; conjugation by a, b, ab acts on (x, y, z) by the sign
patterns (+,-,-), (-,+,-), (-,-,+).  Single-threaded, exact rationals.
"""
from fractions import Fraction as F

def mat(rows):
    return [[F(c) for c in r] for r in rows]

def mul(X, Y):
    return [[sum(X[i][k] * Y[k][j] for k in range(4)) for j in range(4)] for i in range(4)]

def inv_affine(X):
    # inverse of v -> D v + t with D diagonal +-1
    D = [X[i][i] for i in range(3)]
    t = [X[i][3] for i in range(3)]
    R = [[F(0)] * 4 for _ in range(4)]
    for i in range(3):
        R[i][i] = 1 / D[i]
        R[i][3] = -t[i] / D[i]
    R[3][3] = F(1)
    return R

def power(X, n):
    R = mat([[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]])
    B = X if n >= 0 else inv_affine(X)
    for _ in range(abs(n)):
        R = mul(R, B)
    return R

h = F(1, 2)
a = [[F(1),0,0,h],[0,F(-1),0,h],[0,0,F(-1),0],[0,0,0,F(1)]]
b = [[F(-1),0,0,0],[0,F(1),0,h],[0,0,F(-1),h],[0,0,0,F(1)]]
a = [[F(c) for c in r] for r in a]
b = [[F(c) for c in r] for r in b]
ai, bi = inv_affine(a), inv_affine(b)
x, y, z = power(a, 2), power(b, 2), power(mul(a, b), 2)

def show(name, X):
    print(name, "linear diag", [str(X[i][i]) for i in range(3)], "translation", [str(X[i][3]) for i in range(3)])

rel1 = mul(mul(bi, x), b) == power(a, -2)
rel2 = mul(mul(ai, y), a) == power(b, -2)
print("relator b^-1 a^2 b = a^-2 holds:", rel1)
print("relator a^-1 b^2 a = b^-2 holds:", rel2)
show("x=a^2   ", x); show("y=b^2   ", y); show("z=(ab)^2", z)
ok = rel1 and rel2
for gname, g in [("a", a), ("b", b), ("ab", mul(a, b))]:
    gi = inv_affine(g)
    signs = []
    for tname, T in [("x", x), ("y", y), ("z", z)]:
        C = mul(mul(g, T), gi)
        if C == T:
            signs.append("+")
        elif C == inv_affine(T):
            signs.append("-")
        else:
            signs.append("?"); ok = False
    print("conjugation by", gname, "on (x,y,z):", "".join(signs))
print("ALL CHECKS PASS:", ok)
