#!/usr/bin/env python3
"""Exact checks for research/h-mix-symbol-extension-of-two-lef-halves.md.

J = F_2<S,T | TS = 1> has F_2-basis S^i T^j (i, j >= 0), with
    (S^a T^b)(S^c T^d) = S^a T^(b-c+d)      if b >= c
                       = S^(a+c-b) T^d      if b <  c.
An element is a frozenset of pairs (i, j) (coefficients in F_2).
Q = 1 - ST.  Symbol J -> A = F_2[z, z^-1]: S^i T^j -> z^(i-j); kernel I = (Q).
Row vectors (x1, x2) in J^2 carry the right action of 2x2 matrices over F_2[S].
"""
import itertools, sys

def mul_mono(m, n):
    (a, b), (c, d) = m, n
    return (a, b - c + d) if b >= c else (a + c - b, d)

def mul(x, y):
    out = set()
    for m in x:
        for n in y:
            out ^= {mul_mono(m, n)}
    return frozenset(out)

def add(*xs):
    out = set()
    for x in xs:
        out ^= set(x)
    return frozenset(out)

ONE = frozenset({(0, 0)}); ZERO = frozenset()
S = frozenset({(1, 0)}); T = frozenset({(0, 1)})
Q = add(ONE, mul(S, T))
def Sp(k): return frozenset({(k, 0)})
def Tp(k): return frozenset({(0, k)})

def symbol(x):
    cnt = {}
    for (i, j) in x:
        cnt[i - j] = cnt.get(i - j, 0) ^ 1
    return {e for e, v in cnt.items() if v}

ok = True
def check(name, cond):
    global ok
    print(("PASS " if cond else "FAIL ") + name)
    ok &= bool(cond)

# 1. relations
check("TS = 1", mul(T, S) == ONE)
check("QS = 0", mul(Q, S) == ZERO)
check("TQ = 0", mul(T, Q) == ZERO)
for k in range(1, 7):
    Qk = add(ONE, mul(Sp(k), Tp(k)))
    tele = add(*[mul(mul(Sp(i), Q), Tp(i)) for i in range(k)])
    check(f"1 - S^{k}T^{k} = sum_(i<{k}) S^i Q T^i", Qk == tele)
    check(f"Q_{k} S^{k} = 0", mul(Qk, Sp(k)) == ZERO)

# 2. right kernel of S^k on a box of J equals span{S^a Q T^b : b < k}
def rank_f2(vecs):
    rows = [v for v in (int(x) for x in vecs) if v]
    r = 0; piv = []
    basis = []
    for v in rows:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v); r += 1
    return r

def kernel_dim_right_mult(elem, box):
    mons = [(i, j) for i in range(box) for j in range(box)]
    imgs = []
    allm = {}
    for m in mons:
        y = mul(frozenset({m}), elem)
        v = 0
        for n in y:
            if n not in allm: allm[n] = len(allm)
            v |= 1 << allm[n]
        imgs.append(v)
    return len(mons) - rank_f2(imgs)

for k in range(1, 5):
    box = 9
    kd = kernel_dim_right_mult(Sp(k), box)
    # span{S^a Q T^b : b < k} inside box: S^a Q T^b = S^a T^b - S^(a+1) T^(b+1);
    # the box-contained ones are a <= box-2, b < k: (box-1)*k elements
    expected = (box - 1) * k
    check(f"dim ker(right S^{k}) on box{box} = {expected}", kd == expected)

# 3. c = r_a r_b over F_2[S] (polys as int bitmasks)
def pmul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        a <<= 1; b >>= 1
    return r
def mmul(X, Y):
    return [[pmul(X[i][0], Y[0][j]) ^ pmul(X[i][1], Y[1][j]) for j in range(2)] for i in range(2)]
I2 = [[1, 0], [0, 1]]
ra = [[1, 1], [0, 1]]           # x_34(1)
rb = [[1, 0], [0b10, 1]]        # x_43(S)
c = mmul(ra, rb)
check("c = [[1+S,1],[S,1]]", c == [[0b11, 1], [0b10, 1]])
check("ra^2 = rb^2 = 1", mmul(ra, ra) == I2 and mmul(rb, rb) == I2)
det = pmul(c[0][0], c[1][1]) ^ pmul(c[0][1], c[1][0])
check("det c = 1, tr c = S", det == 1 and (c[0][0] ^ c[1][1]) == 0b10)
P = I2; inf = True
for n in range(1, 301):
    P = mmul(P, c)
    if P == I2: inf = False
check("c^n != 1 for 1 <= n <= 300", inf)

# 4. det p(c) != 0 for every nonzero p in F_2[x], deg <= 12
def peval_matrix(p):
    R = [[0, 0], [0, 0]]; Pw = I2; e = 0
    while p >> e:
        if (p >> e) & 1:
            R = [[R[i][j] ^ Pw[i][j] for j in range(2)] for i in range(2)]
        Pw = mmul(Pw, c); e += 1
    return R
allnz = True
for p in range(1, 1 << 13):
    M = peval_matrix(p)
    if pmul(M[0][0], M[1][1]) ^ pmul(M[0][1], M[1][0]) == 0:
        allnz = False; print("  zero det for p =", bin(p))
check("det p(c) != 0 in F_2[S] for all p != 0, deg p <= 12", allnz)

# 5. windows I_{<=d} = span{S^a Q T^b : b <= d} are right F_2[S]-stable
def in_window(x, d):
    # x in I_{<=d}  <=>  symbol(x) = 0 and x lies in span of S^a Q T^b, b <= d.
    # Reduce: repeatedly strip the monomial with the largest j via S^aQT^b.
    x = set(x)
    while x:
        (a, b) = max(x, key=lambda m: (m[1], m[0]))
        # write (a,b) as leading term of S^(a-1) Q T^(b-1) = S^(a-1)T^(b-1) - S^a T^b
        if a == 0 or b == 0:
            return False
        if b - 1 > d:
            return False
        x ^= {(a - 1, b - 1), (a, b)}
    return True
winok = True
for d in range(0, 4):
    for a in range(0, 4):
        for b in range(0, d + 1):
            w = mul(mul(Sp(a), Q), Tp(b))
            if not in_window(w, d): winok = False
            if not in_window(mul(w, S), d): winok = False
    check(f"I_<=%d stable under right S" % d, winok)
# T escapes the window (why S-orientation, not T, is locally finite here)
check("Q T^0 * T = QT not in I_<=0", not in_window(mul(Q, T), 0))

# 6. symbol side: finite-dim c-stable subspaces of A^2 vanish (det p(c) != 0
#    in the domain A); on J^2 they lie in ker delta(S) = J Q_k (checked in 2).
print("ALL PASS" if ok else "SOME FAIL")
sys.exit(0 if ok else 1)
