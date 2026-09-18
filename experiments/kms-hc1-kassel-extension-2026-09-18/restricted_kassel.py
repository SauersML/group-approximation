"""Restricted Kassel extension of the truncated Iwahori Lie algebra.

N = (L_p / height > n) + F_p z, n = 3mp, with bracket
    [x, y]_N = [x, y]_L + omega(x, y) z,   omega(X t^a, Y t^b) = a tr(XY) [a + b = mp].

Checks, over F_p:
  (1) omega is a 2-cocycle on the truncation (Jacobi in N on all basis triples);
  (2) Jacobson's criterion: for every homogeneous basis vector e of N (root vectors
      E_ij t^k and Cartan vectors h t^k), (ad_N e)^p = ad_N(e^[p]) on every basis x,
      with e^[p] = e^p (matrix power) and zero z-component;
  (3) a = E12, b = E23, c = t E31 have p-th matrix power 0 and satisfy the six
      Serre relations in N, and z lies in [N, N].
By Jacobson (Lie Algebras, V.7 Thm 11), (2) gives a unique p-map on N with these
values on the basis; with (3), N is a restricted quotient of
FreeRes(a,b,c)/(a^[p], b^[p], c^[p], Serre) whose height-n piece exceeds that of
L_p by the Kassel vector z.

Usage: python3 restricted_kassel.py p m   (prints PASS/FAIL counts)
"""
import sys
import itertools

p = int(sys.argv[1]); m = int(sys.argv[2])
n = 3 * m * p            # height of z
K = m * p + 1            # loop exponents 0..K suffice (height <= n)


def height(i, j, k):
    return (j - i) + 3 * k


# element: (dict {(i,j,k): coeff}, zcoef); matrices entries E_ij t^k
def trunc(d):
    return {key: v % p for key, v in d.items() if v % p and height(*key) <= n and height(*key) >= 1}


def mat_mul(A, B):
    C = {}
    for (i, j, k), u in A.items():
        for (j2, l, k2), v in B.items():
            if j2 == j:
                key = (i, l, k + k2)
                if height(*key) <= n + 3:      # keep a margin; truncated later
                    C[key] = (C.get(key, 0) + u * v) % p
    return C


def omega(A, B):
    s = 0
    for (i, j, a), u in A.items():
        for (j2, i2, b), v in B.items():
            if j2 == j and i2 == i and a + b == m * p:
                s += a * u * v
    return s % p


def br(x, y):
    A, _ = x; B, _ = y
    C = mat_mul(A, B)
    for key, v in mat_mul(B, A).items():
        C[key] = (C.get(key, 0) - v) % p
    return (trunc(C), omega(A, B))


def add(x, y, c=1):
    C = dict(x[0])
    for key, v in y[0].items():
        C[key] = (C.get(key, 0) + c * v) % p
    return (trunc(C), (x[1] + c * y[1]) % p)


def is_zero(x):
    return not x[0] and x[1] % p == 0


def power(A, e):
    R = {(i, i, 0): 1 for i in range(3)}
    for _ in range(e):
        R = mat_mul(R, A)
    return R


# basis of L_p up to height n
basis = []
for k in range(K + 1):
    for i in range(3):
        for j in range(3):
            if i != j and 1 <= height(i, j, k) <= n:
                basis.append(({(i, j, k): 1}, 0))
    if k >= 1 and 3 * k <= n:
        basis.append(({(0, 0, k): 1, (1, 1, k): p - 1}, 0))
        basis.append(({(1, 1, k): 1, (2, 2, k): p - 1}, 0))
Z = ({}, 1)


def deg(x):
    return min(height(*key) for key in x[0])


fails = 0; checks = 0
# (1) cocycle / Jacobi
for x, y, w in itertools.combinations(basis, 3):
    if deg(x) + deg(y) + deg(w) != n:
        continue
    s = add(add(br(x, br(y, w)), br(y, br(w, x))), br(w, br(x, y)))
    checks += 1
    if not is_zero(s):
        fails += 1
print("jacobi triples of total height n:", checks, "fails:", fails)

# (2) Jacobson criterion
f2 = 0; c2 = 0
for e in basis:
    d = deg(e)
    ep = power(e[0], p)
    # e^[p] = e^p for root vectors (0) and Cartan h t^k -> h^p t^{pk}
    ep_el = (trunc(ep), 0)
    for x in basis:
        if deg(x) + p * d > n:
            continue
        lhs = x
        for _ in range(p):
            lhs = br(e, lhs)
        rhs = br(ep_el, x)
        c2 += 1
        if not is_zero(add(lhs, rhs, -1)):
            f2 += 1
print("Jacobson (ad e)^p = ad(e^[p]) checks:", c2, "fails:", f2)

# (3) generators
a = ({(0, 1, 0): 1}, 0); b = ({(1, 2, 0): 1}, 0); c = ({(2, 0, 1): 1}, 0)
serre = [br(br(a, b), a), br(br(a, b), b), br(br(b, c), b), br(br(b, c), c), br(br(a, c), a), br(br(a, c), c)]
print("Serre relations vanish in N:", all(is_zero(s) for s in serre))
print("a^p, b^p, c^p zero:", all(not trunc(power(g[0], p)) for g in (a, b, c)))
# z in [N,N]: omega(E12 t^1, E21 t^{mp-1}) = 1
print("z = [E12 t, E21 t^(mp-1)] - [..]_L, omega =", omega({(0, 1, 1): 1}, {(1, 0, m * p - 1): 1}))
# omega is not a coboundary f([x,y]): [E12 t^a, E21 t^(mp-a)]_L = h1 t^(mp) for a = 1, 2,
# but omega takes the values 1 and 2 there.
x1, y1 = ({(0, 1, 1): 1}, 0), ({(1, 0, m * p - 1): 1}, 0)
x2, y2 = ({(0, 1, 2): 1}, 0), ({(1, 0, m * p - 2): 1}, 0)
same_L = br(x1, y1)[0] == br(x2, y2)[0]
noncob = same_L and br(x1, y1)[1] != br(x2, y2)[1]
print("omega not a coboundary (same L-bracket, omega 1 vs 2):", noncob)
print("RESULT", "PASS" if fails == 0 and f2 == 0 and noncob else "FAIL")
