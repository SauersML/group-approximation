#!/usr/bin/env python3
"""Checks for monomial-twisted-level-subpairs-cannot-certify-rank-three.

Elements of G = EL_3(R) x| SL_d(Z) are pairs (u, s): u a 3x3 Laurent matrix, s in SL_d(Z),
(u, s)(u', s') = (u * s^(u'), s s'), where s^ substitutes x^m -> x^(s m).
Checks:
 (A) loop identity (T1-a) for random monomial twists u = D P and random s;
 (B) explicit certificate: SL_3(Z) on Z^3, diagonal + signed-permutation twists on generators,
     the (T1) recipe yields e_xy(1) for all six (x, y);
 (C) Borel twists: the loop closes only into the lowest root (x, y) = (3, 1) (remark (T5));
 (D) E(R, I^2) <= E(I): z_ij(bc, r) = [1 + b v e_k^T, 1 + c e_k w^T] (lemma (T4));
 (E) finite-index lemma (T2) on a congruence subgroup: -e_1 in cone(Gamma(2) O), LP certificate.
Exit 0 iff all checks pass.
"""
import itertools, random, sys
import sympy as sp
import numpy as np
from scipy.optimize import linprog

d = 3
X = sp.symbols('x1:%d' % (d + 1))
random.seed(7)
FAIL = []

def mono(m):
    return sp.Mul(*[X[i] ** int(m[i]) for i in range(d)])

def subst(expr, s):
    # x_i -> x^(s e_i) = prod_j x_j^(s[j][i])
    return sp.expand(expr.subs({X[i]: mono([s[j, i] for j in range(d)]) for i in range(d)},
                               simultaneous=True))

def shat(u, s):
    return u.applyfunc(lambda e: subst(e, s))

def mul(g, h):
    return (sp.simplify(g[0] * shat(h[0], g[1])), g[1] * h[1])

def inv(g):
    si = g[1].inv()
    return (shat(g[0].inv(), si), si)

def conj(g, e):  # g (e,1) g^-1, returns matrix
    return sp.simplify(g[0] * shat(e, g[1]) * g[0].inv())

def E(a, b, t):
    M = sp.eye(3); M[a, b] = t; return M

def comm(A, B):
    return sp.simplify(A * B * A.inv() * B.inv())

def is_elem(M, a, b):
    Z = sp.simplify(M - sp.eye(3))
    return all(sp.simplify(Z[i, j]) == 0 for i in range(3) for j in range(3) if (i, j) != (a, b))

def third(a, b):
    return 3 - a - b

def check(name, ok):
    print(('PASS ' if ok else 'FAIL ') + name)
    if not ok: FAIL.append(name)

# ---------- (A) loop identity
def rand_mono_twist():
    perm = random.choice(list(itertools.permutations(range(3))))
    P = sp.zeros(3)
    for a in range(3): P[perm[a], a] = 1
    D = sp.diag(*[random.choice([1, -1]) * mono([random.randint(-3, 3) for _ in range(d)]) for _ in range(3)])
    u = D * P
    u = u * sp.diag(1, 1, 1 / u.det())  # force det 1 (adjust a column by a unit monomial)
    return sp.simplify(u), perm

S3gens = [np.eye(3, dtype=int) + np.eye(3, k=1, dtype=int), np.eye(3, dtype=int) + np.eye(3, k=-1, dtype=int),
          np.array([[1, 0, 1], [0, 1, 0], [0, 0, 1]]), np.array([[0, 1, 0], [0, 0, 1], [1, 0, 0]])]
okA = True
for trial in range(6):
    u, perm = rand_mono_twist()
    s = sp.Matrix(random.choice(S3gens))
    c = (u, s)
    x, y = random.sample(range(3), 2); z = third(x, y)
    a, b = perm.index(y), perm.index(z)
    m, mp_ = [random.randint(1, 2) for _ in range(d)], [random.randint(1, 2) for _ in range(d)]
    beta_p = [random.randint(0, 2) for _ in range(d)]
    T1 = conj(c, E(a, b, mono(m))); T2 = conj(c, E(b, a, mono(mp_)))
    L = comm(comm(E(x, y, 5 * mono(beta_p)), T1), T2)
    sm = [sum(int(s[i, j]) * (m[j] + mp_[j]) for j in range(d)) for i in range(d)]
    target = E(x, y, 5 * mono([beta_p[i] + sm[i] for i in range(d)]))
    okA &= sp.simplify(L - target) == sp.zeros(3)
check('(A) loop [[e_xy(b), c e_ab c^-1], c e_ba c^-1] = e_xy(b x^(s(m+m\'))) for monomial twists', okA)

# ---------- (B) explicit certificate over H = SL_3(Z) with twisted generator lifts, k = 1
def eZ(i, j, t):
    M = sp.eye(3); M[i, j] = t; return M
g12, g21 = eZ(0, 1, 1), eZ(1, 0, 1)            # nonnegative generators of SL_3(Z) (with the other e_ij(1))
u1 = sp.diag(X[0] ** 2 * X[2] ** -1, X[1] ** -3, X[0] ** -2 * X[1] ** 3 * X[2])   # diagonal twist
P = sp.Matrix([[0, -1, 0], [1, 0, 0], [0, 0, 1]])                                   # signed permutation
u2 = sp.simplify(sp.diag(X[2] ** 4, X[0] ** -1 * X[1], X[0] * X[1] ** -1 * X[2] ** -4) * P)
c12, c21 = (u1, g12), (u2, g21)
ctau = mul(c12, inv(c21))                      # lift of tau = e_12(1) e_21(-1); tau(2 e_1) = -2 e_2
tau = ctau[1]
okB = (list(tau * sp.Matrix([2, 0, 0])) == [0, -2, 0])
utau = ctau[0]
pattern = [[sp.simplify(utau[i, j]) != 0 for j in range(3)] for i in range(3)]
okB &= all(sum(r) == 1 for r in pattern) and all(sum(pattern[i][j] for i in range(3)) == 1 for j in range(3))
perm = [next(i for i in range(3) if pattern[i][a]) for a in range(3)]       # u e_a ~ e_perm[a]
print('   twist of the lift of tau:', list(utau))
for x, y in itertools.permutations(range(3), 2):
    z = third(x, y); a, b = perm.index(y), perm.index(z)
    T1 = conj(ctau, E(a, b, X[0])); T2 = conj(ctau, E(b, a, X[0]))
    okB &= is_elem(T1, y, z) and is_elem(T2, z, y)
    Lxy = comm(comm(E(x, y, X[1] ** 2), T1), T2)
    okB &= sp.simplify(Lxy - E(x, y, 1)) == sp.zeros(3)
check('(B) SL_3(Z), twisted lifts: e_xy(1) = [[e_xy(x_2^2), c e_ab(x_1) c^-1], c e_ba(x_1) c^-1] for all six (x,y)', okB)

# ---------- (C) Borel twists: loop into (x,y) through z closes iff (u^-1) vanishes at (z,x),(y,x),(y,z)
f = X[0] ** -1 + X[1] ** -2
uB = sp.Matrix([[1, 0, 0], [f, 1, 0], [X[2] ** -1, f ** 2, 1]])     # lower unitriangular, Laurent entries
cB = (uB, eZ(0, 1, 1))
closes = []
for x, y in itertools.permutations(range(3), 2):
    z = third(x, y)
    T1 = conj(cB, E(y, z, X[0] ** 2)); T2 = conj(cB, E(z, y, X[0] ** 2))
    Lxy = comm(comm(E(x, y, X[1] ** 2), T1), T2)
    if is_elem(Lxy, x, y): closes.append((x + 1, y + 1))
print('   Borel loop closes into (x,y) =', closes)
check('(C) lower-triangular twist: loop closes only into the lowest root (3,1)', closes == [(3, 1)])

# ---------- (D) z_ij(bc, r) = e_ji(r) e_ij(bc) e_ji(-r) is a commutator of E(I)-elements
bb, cc, r = sp.symbols('b c r')
i, j, k = 0, 1, 2
Z = E(j, i, r) * E(i, j, bb * cc) * E(j, i, -r)
Aleft = sp.simplify(E(i, k, bb) * E(j, k, r * bb))          # 1 + b v e_k^T, v = e_i + r e_j
Aright = sp.simplify(E(k, j, cc) * E(k, i, -r * cc))        # 1 + c e_k w^T, w = e_j - r e_i
check('(D) z_ij(bc, r) = [e_ik(b) e_jk(rb), e_kj(c) e_ki(-rc)]', sp.simplify(Z - comm(Aleft, Aright)) == sp.zeros(3))

# ---------- (E) finite index: -e_1 in cone(Gamma(2) . O) for the congruence subgroup Gamma(2) of SL_3(Z)
gens = [np.eye(3, dtype=int) + 2 * np.eye(3, dtype=int)[:, [p]] @ np.eye(3, dtype=int)[[q], :]
        for p in range(3) for q in range(3) if p != q]
gens += [np.round(np.linalg.inv(g)).astype(int) for g in gens]
vecs = set()
for w in itertools.product(range(len(gens)), repeat=2):
    g = np.eye(3, dtype=int)
    for t in w: g = g @ gens[t]
    for col in range(3): vecs.add(tuple(g[:, col]))
V = np.array(sorted(vecs)).T
res = linprog(np.ones(V.shape[1]), A_eq=V, b_eq=np.array([-1, 0, 0]), bounds=(0, None), method='highs')
check('(E) -e_1 in cone(Gamma(2) O): LP feasible', res.status == 0)

print('ALL PASS' if not FAIL else 'FAILURES: %s' % FAIL)
sys.exit(0 if not FAIL else 1)
