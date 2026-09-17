"""Sanity check of the sign conventions used in
research/steinberg-images-die-in-torsion-free-groups-proof.md.

The proof itself is a derivation from the Steinberg relations; this script only
confirms, in the faithful-enough quotient EL_3(M_2(Z)) (a noncommutative
coefficient ring), that the displayed conjugation formulas carry the stated
signs, that h w h^-1 = w^-1, and that the idempotent Weyl word of (W2) has
order exactly 4.  Commutator convention: [a,b] = a b a^-1 b^-1.
"""


def mm(a, b):
    n = len(a)
    return [[sum(a[i][k] * b[k][j] for k in range(n)) for j in range(n)]
            for i in range(n)]


def eye():
    return [[int(i == j) for j in range(6)] for i in range(6)]


def x(i, j, r):
    m = eye()
    for a in range(2):
        for b in range(2):
            m[2 * i + a][2 * j + b] += r[a][b]
    return m


def neg(r):
    return [[-v for v in row] for row in r]


def prod(*ms):
    p = eye()
    for m in ms:
        p = mm(p, m)
    return p


def comm(a, b, ainv, binv):
    return prod(a, b, ainv, binv)


ONE = [[1, 0], [0, 1]]
R = [[2, -3], [5, 7]]
S = [[-4, 1], [0, 3]]

w = prod(x(0, 1, ONE), x(1, 0, neg(ONE)), x(0, 1, ONE))
winv = prod(x(0, 1, neg(ONE)), x(1, 0, ONE), x(0, 1, neg(ONE)))
assert mm(w, winv) == eye()

# Steinberg commutator relation [x_ij(a), x_jk(b)] = x_ik(ab)
ab = [[sum(R[i][k] * S[k][j] for k in range(2)) for j in range(2)]
      for i in range(2)]
assert comm(x(0, 1, R), x(1, 2, S), x(0, 1, neg(R)), x(1, 2, neg(S))) == x(0, 2, ab)

# (P1)-(P4): conjugation by w on the four mixed roots
assert prod(w, x(0, 2, R), winv) == x(1, 2, neg(R))
assert prod(w, x(1, 2, R), winv) == x(0, 2, R)
assert prod(w, x(2, 0, R), winv) == x(2, 1, neg(R))
assert prod(w, x(2, 1, R), winv) == x(2, 0, R)
# (P5)-(P6)
assert prod(w, x(0, 1, R), winv) == x(1, 0, neg(R))
assert prod(w, x(1, 0, R), winv) == x(0, 1, neg(R))

# h = v^2 with v the (1,3) Weyl word inverts w
v = prod(x(0, 2, ONE), x(2, 0, neg(ONE)), x(0, 2, ONE))
vinv = prod(x(0, 2, neg(ONE)), x(2, 0, ONE), x(0, 2, neg(ONE)))
h = mm(v, v)
hinv = mm(vinv, vinv)
assert prod(h, x(0, 1, R), hinv) == x(0, 1, neg(R))
assert prod(h, x(1, 0, R), hinv) == x(1, 0, neg(R))
assert prod(h, w, hinv) == winv

# (W2): idempotent Weyl word has order exactly 4
E = [[1, 0], [0, 0]]
we = prod(x(0, 1, E), x(1, 0, neg(E)), x(0, 1, E))
assert prod(we, we) != eye()
assert prod(we, we, we, we) == eye()

print("all sign checks passed")
