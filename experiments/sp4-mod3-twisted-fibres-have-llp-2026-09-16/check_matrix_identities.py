"""Sanity checks for the matrix identities in
research/artifacts/sp4-mod3-twisted-fibre-f2xf2-calibration-2026-09-16.md.

Exact integer / rational arithmetic only.  Checks:
  (1) Lemma 3.2P: a^4 = I, a^2 = b^3 = -I, a^{-1} b = tau, the Euclidean
      reduction, and ping-pong on random alternating words (numerically on an
      irrational point, exact Moebius action on sqrt(2)-type points via Q(sqrt2)).
  (2) Section 4: block-diagonal SL_2 x SL_2 is symplectic.
  (3) Section 5: m(A) n(S) symplectic, conjugation formula, rho(U) symplectic
      for U = R_theta at rational points of the circle, J = rho(-i I).
  (4) Section 6: n(x,y,u) symplectic, group law, commutator n(0,0,2),
      Levi decomposition of random elements of P_K(Z).
  (5) Lemma 3.3: random nontrivial reduced words in Sanov matrices are != I.
Run: timeout 600 python3 check_matrix_identities.py
"""
from fractions import Fraction as Fr
import random

random.seed(20260916)

def mul(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return [[sum(A[i][k] * B[k][j] for k in range(m)) for j in range(p)] for i in range(n)]

def eye(n):
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]

def mpow(A, k):
    R = eye(len(A))
    for _ in range(k):
        R = mul(R, A)
    return R

def T(A):
    return [list(r) for r in zip(*A)]

def neg(A):
    return [[-x for x in r] for r in A]

ok = True
def check(cond, msg):
    global ok
    if not cond:
        ok = False
        print("FAIL:", msg)

# ---------- (1) Lemma 3.2P ----------
a = [[0, -1], [1, 0]]
b = [[0, -1], [1, 1]]
I2 = eye(2)
check(mpow(a, 4) == I2, "a^4 = I")
check(mpow(a, 2) == neg(I2), "a^2 = -I")
check(mpow(b, 2) == [[-1, -1], [1, 0]], "b^2")
check(mpow(b, 3) == neg(I2), "b^3 = -I")
ainv = [[0, 1], [-1, 0]]
check(mul(a, ainv) == I2, "a^{-1}")
tau = [[1, 1], [0, 1]]
check(mul(ainv, b) == tau, "a^{-1} b = tau")

def euclid_word(g):
    """Return a word in a, tau (as list of (name, exponent)) equal to g, following step 2."""
    p, q = g[0]
    r, s = g[1]
    if r == 0:
        assert p * s == 1 and p == s
        word = []
        if p == -1:
            word.append(("a", 2))
        word.append(("tau", p * q))
        return word
    k = (-p) // r if r > 0 else None
    # choose k with 0 <= p + k r < |r|
    k = 0
    rem = p % abs(r)
    k = (rem - p) // r
    assert 0 <= p + k * r < abs(r)
    h = mul(a, mul(tpow(k), g))
    assert abs(h[1][0]) < abs(r)
    # g = tau^{-k} a^{-1} h
    return [("tau", -k), ("a", 3)] + euclid_word(h)

def tpow(k):
    return [[1, k], [0, 1]]

def evalword(word):
    R = I2
    for name, e in word:
        if name == "a":
            R = mul(R, mpow(a, e % 4))
        else:
            R = mul(R, tpow(e))
    return R

for _ in range(300):
    g = I2
    for _ in range(random.randint(0, 12)):
        g = mul(g, random.choice([a, b, ainv, tau, [[1, -1], [0, 1]]]))
    check(evalword(euclid_word(g)) == g, "Euclidean reduction reproduces g")

# ping-pong: exact action on x = sqrt(2) + t represented in Q(sqrt 2) as (u, v) = u + v sqrt2
def qs_div(x, y):
    (u1, v1), (u2, v2) = x, y
    den = u2 * u2 - 2 * v2 * v2
    return ((u1 * u2 - 2 * v1 * v2) / den, (v1 * u2 - u1 * v2) / den)

def act(g, x):
    (p, q), (r, s) = g
    num = (p * x[0] + q, p * x[1])
    den = (r * x[0] + s, r * x[1])
    return qs_div(num, den)

def sign(x):
    u, v = x
    val = float(u) + float(v) * 2 ** 0.5
    return val

for _ in range(500):
    k = random.randint(1, 8)
    exps = [random.choice([1, 2]) for _ in range(k)]
    # type (i): Y^{e1} X Y^{e2} ... X Y^{ek}
    g = mpow(b, exps[0])
    for e in exps[1:]:
        g = mul(g, mul(a, mpow(b, e)))
    x = (Fr(random.randint(1, 50), random.randint(1, 50)), Fr(1))  # positive irrational
    y = act(g, x)
    check(sign(y) < 0, "type (i) word maps Omega_+ into Omega_-")
    check(g != I2 and g != neg(I2), "type (i) word is nontrivial in PSL_2")

# ---------- (2)-(4) symplectic checks ----------
# basis order for sections 1,4,6: (e1, f1, e2, f2); b(e_i,f_j)=delta
Omega4 = [[0, 1, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 1], [0, 0, -1, 0]]
def is_sp(g, Om):
    return mul(T(g), mul(Om, g)) == Om

def block_diag(g1, g2):
    return [[g1[0][0], g1[0][1], 0, 0], [g1[1][0], g1[1][1], 0, 0],
            [0, 0, g2[0][0], g2[0][1]], [0, 0, g2[1][0], g2[1][1]]]

for _ in range(100):
    g1 = I2; g2 = I2
    for _ in range(6):
        g1 = mul(g1, random.choice([a, b, tau]))
        g2 = mul(g2, random.choice([a, b, tau]))
    check(is_sp(block_diag(g1, g2), Omega4), "block diagonal SL2 x SL2 symplectic")
    check(mul(block_diag(g1, I2), block_diag(I2, g2)) == mul(block_diag(I2, g2), block_diag(g1, I2)), "factors commute")

# Section 5: basis (e1,e2,f1,f2), J=[[0,I],[-I,0]]
J = [[0, 0, 1, 0], [0, 0, 0, 1], [-1, 0, 0, 0], [0, -1, 0, 0]]
def blocks(A, B, C, D):
    return [A[0] + B[0], A[1] + B[1], C[0] + D[0], C[1] + D[1]]
def inv2(A):
    d = Fr(A[0][0] * A[1][1] - A[0][1] * A[1][0])
    return [[A[1][1] / d, -A[0][1] / d], [-A[1][0] / d, A[0][0] / d]]
Z2 = [[0, 0], [0, 0]]
def m(A):
    return blocks(A, Z2, Z2, T(inv2(A)))
def n(S):
    return blocks(I2, S, Z2, I2)
for _ in range(200):
    A = [[random.randint(-5, 5) for _ in range(2)] for _ in range(2)]
    if A[0][0] * A[1][1] - A[0][1] * A[1][0] == 0:
        continue
    s1, s2, s3 = (random.randint(-5, 5) for _ in range(3))
    S = [[s1, s2], [s2, s3]]
    g = mul(m(A), n(S))
    check(is_sp(g, J), "m(A)n(S) symplectic")
    check(g == blocks(A, mul(A, S), Z2, T(inv2(A))), "m(A)n(S) block form")
    check(mul(mul(m(A), n(S)), m(inv2(A))) == n(mul(A, mul(S, T(A)))), "conjugation formula")

def rho(X, Y):
    return blocks(X, [[-y for y in r] for r in Y], Y, X)
check(rho(Z2, neg(I2)) == J, "J = rho(-i I)")
# rational points on the circle: cos = (1-t^2)/(1+t^2), sin = 2t/(1+t^2)
for t in [Fr(0), Fr(1, 2), Fr(3), Fr(-7, 5)]:
    c = (1 - t * t) / (1 + t * t); s_ = 2 * t / (1 + t * t)
    R = [[c, -s_], [s_, c]]
    check(rho(R, Z2) == m(R), "rho(R_theta) = m(R_theta)")
    check(is_sp(rho(R, Z2), J), "rho(R_theta) symplectic")
    # a unitary with complex entries: U = [[c, -s i],[ -s i, c]]? use X=[[c,0],[0,c]], Y=[[0,-s],[-s,0]]
    U = rho([[c, 0], [0, c]], [[0, -s_], [-s_, 0]])
    check(is_sp(U, J), "rho(unitary) symplectic")
eps = [[1, 0, 0, 0], [0, -1, 0, 0], [0, 0, 1, 0], [0, 0, 0, -1]]
check(eps == m([[1, 0], [0, -1]]), "epsilon = m(diag(1,-1))")

# Section 6: basis (e1,f1,e2,f2); columns are images of basis vectors
def nK(x, y, u):
    # images: e1->e1, f1->f1+u e1+y e2 - x f2, e2->e2+x e1, f2->f2+y e1
    cols = [[1, 0, 0, 0], [u, 1, y, -x], [x, 0, 1, 0], [y, 0, 0, 1]]
    return T(cols)
for _ in range(300):
    x, y, u, x2, y2, u2 = (random.randint(-6, 6) for _ in range(6))
    g, h = nK(x, y, u), nK(x2, y2, u2)
    check(is_sp(g, Omega4), "n(x,y,u) symplectic")
    check(mul(g, h) == nK(x + x2, y + y2, u + u2 + x * y2 - x2 * y), "Klingen group law")
check(mul(mul(nK(1, 0, 0), nK(0, 1, 0)), mul(nK(-1, 0, 0), nK(0, -1, 0))) == nK(0, 0, 2), "commutator = n(0,0,2)")
# general symplectic unipotent with the flag: v, w free -> forced v=y, w=-x
for _ in range(50):
    x, y, u, v, w = (random.randint(-4, 4) for _ in range(5))
    cols = [[1, 0, 0, 0], [u, 1, v, w], [x, 0, 1, 0], [y, 0, 0, 1]]
    g = T(cols)
    check(is_sp(g, Omega4) == (v == y and w == -x), "Klingen parametrization conditions")

# Levi decomposition: random element of P_K(Z) = nK * l, l = (+-1 on P1) x SL2 on P2
def lev(lam, M):
    return [[lam, 0, 0, 0], [0, lam, 0, 0], [0, 0, M[0][0], M[0][1]], [0, 0, M[1][0], M[1][1]]]
for _ in range(200):
    M = I2
    for _ in range(5):
        M = mul(M, random.choice([a, b, tau]))
    lam = random.choice([1, -1])
    g = mul(nK(*(random.randint(-5, 5) for _ in range(3))), lev(lam, M))
    check(is_sp(g, Omega4), "P_K element symplectic")
    check([g[i][0] for i in range(4)] == [lam, 0, 0, 0], "g e1 = lambda e1")
    # recover l(g): lambda from g e1, M from the (e2,f2) block
    Mg = [[g[2][2], g[2][3]], [g[3][2], g[3][3]]]
    l = lev(g[0][0], Mg)
    linv = lev(g[0][0], inv2(Mg))
    ng = mul(g, linv)
    x, y, u = ng[0][2], ng[0][3], ng[0][1]
    check(ng == nK(x, y, u), "g l(g)^{-1} lies in N(Z)")

# ---------- (5) Sanov ----------
M1 = [[1, 2], [0, 1]]; M2 = [[1, 0], [2, 1]]
def spow(M, k):
    if k >= 0:
        return mpow(M, k)
    Mi = [[M[1][1], -M[0][1]], [-M[1][0], M[0][0]]]
    return mpow(Mi, -k)
for _ in range(500):
    k = random.randint(1, 7)
    start = random.choice([0, 1])
    g = I2
    for i in range(k):
        e = random.choice([-3, -2, -1, 1, 2, 3])
        g = mul(g, spow(M1 if (i + start) % 2 == 0 else M2, e))
    check(g != I2, "Sanov reduced word nontrivial")

print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
