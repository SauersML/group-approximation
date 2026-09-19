"""Checks the matrix inputs of kms-hc1-cartan-relator-is-tautological-mod-symmetry.

Usage: python3 symmetry_check.py p M   (power series truncated mod t^M)

1. Power maps: tau = Ad(diag(d)) o (t -> mu t) sends x12(1), x23(1), x31(t)
   to x12(al), x23(be), x31(ga t) for all (al,be,ga) in (F_p^*)^3.
2. Rotation Ad(pi), pi = [[0,1,0],[0,0,1],[t,0,0]]: a -> c, b -> a, c -> b.
3. Flip theta(X) = J X^(-T) J^(-1), J = antidiag(1,-1,1): a <-> b, c -> c^(-1); composed with
   power maps; the printed images are root elements x_ij(lam t^k).
4. Lie action of rotation and flip on the Cartan (h_A, h_B, h_C) is the
   permutation action (standard 2-dim rep of S_3).
5. Bruhat identity h(1+s) = x21(-s/(1+s)) x12(1) x21(s) x12(-1/(1+s)), s = t^N.
6. Selection rule: every vertex element (a, b, c and the three centres) has a
   nontrivial character on the subtorus {al*be*ga = 1}, which fixes W_n.
"""
import sys, random, itertools
p = int(sys.argv[1]); M = int(sys.argv[2])
Z = [0] * M
def padd(f, g): return [(x + y) % p for x, y in zip(f, g)]
def pmul(f, g):
    r = [0] * M
    for i, x in enumerate(f):
        if x:
            for j in range(M - i):
                if g[j]: r[i + j] = (r[i + j] + x * g[j]) % p
    return r
def pinv(f):  # f(0) != 0
    r = [0] * M; r[0] = pow(f[0], p - 2, p)
    for k in range(1, M):
        s = sum(f[i] * r[k - i] for i in range(1, k + 1)) % p
        r[k] = (-s * r[0]) % p
    return r
def const(c): r = [0] * M; r[0] = c % p; return r
def mono(c, k): r = [0] * M; r[k] = c % p; return r
def mmul(A, B):
    return [[ (lambda i, j: [sum(x) % p for x in zip(*[pmul(A[i][l], B[l][j]) for l in range(3)])])(i, j)
              for j in range(3)] for i in range(3)]
def eye(): return [[const(1 if i == j else 0) for j in range(3)] for i in range(3)]
def x(i, j, f):
    A = eye(); A[i - 1][j - 1] = padd(A[i - 1][j - 1], f); return A
def diag(u, v, w): A = [[Z[:] for _ in range(3)] for _ in range(3)]; A[0][0], A[1][1], A[2][2] = u, v, w; return A
def minv(A):  # adjugate, det(A) is a unit series
    c = lambda i, j: padd(pmul(A[(i+1)%3][(j+1)%3], A[(i+2)%3][(j+2)%3]),
                          [(-v) % p for v in pmul(A[(i+1)%3][(j+2)%3], A[(i+2)%3][(j+1)%3])])
    adj = [[c(j, i) for j in range(3)] for i in range(3)]
    det = [sum(v) % p for v in zip(*[pmul(A[0][l], c(0, l)) for l in range(3)])]
    di = pinv(det); return [[pmul(adj[i][j], di) for j in range(3)] for i in range(3)]
def subst(A, mu): return [[[(v * pow(mu, k, p)) % p for k, v in enumerate(e)] for e in row] for row in A]
def ad(g, A): return mmul(mmul(g, A), minv(g))
def eq(A, B): return A == B
ok = True
def check(name, cond):
    global ok
    if not cond: ok = False; print("FAIL", name)
a, b, c = x(1, 2, const(1)), x(2, 3, const(1)), x(3, 1, mono(1, 1))
# 1. power maps
for _ in range(20):
    al, be, ga = [random.randrange(1, p) for _ in range(3)]
    mu = al * be * ga % p
    # d1/d2 = al, d2/d3 = be; take d3 = 1
    d = diag(const(al * be), const(be), const(1))
    tau = lambda A: ad(d, subst(A, mu))
    check("pow a", eq(tau(a), x(1, 2, const(al))))
    check("pow b", eq(tau(b), x(2, 3, const(be))))
    check("pow c", eq(tau(c), x(3, 1, mono(ga, 1))))
# 2. rotation (pi^-1 has a t^-1 entry: conjugate by pi via the formula pi X pi^-1 = Ad)
def rot(A):  # entry (i,j) of A goes to (s(i), s(j)) times t^([i=1]-[j=1]), s: 1->3, 2->1, 3->2
    s = {0: 2, 1: 0, 2: 1}; R = [[Z[:] for _ in range(3)] for _ in range(3)]
    for i in range(3):
        for j in range(3):
            e = A[i][j]; sh = (i == 0) - (j == 0)
            R[s[i]][s[j]] = ([0] + e[:-1]) if sh == 1 else (e[1:] + [0] if sh == -1 else e[:])
            if sh == -1: check("rot integral", e[0] == 0)
    return R
check("rot a->c", eq(rot(a), c)); check("rot b->a", eq(rot(b), a)); check("rot c->b", eq(rot(c), b))
g = mmul(mmul(a, b), minv(c)); check("rot hom", eq(rot(mmul(g, a)), mmul(rot(g), rot(a))))
# 3. flip
J = [[Z[:], Z[:], const(1)], [Z[:], const(-1), Z[:]], [const(1), Z[:], Z[:]]]
def tr(A): return [[A[j][i] for j in range(3)] for i in range(3)]
def flip(A): return mmul(mmul(J, minv(tr(A))), minv(J))
check("flip a", eq(flip(a), x(2, 3, const(1)))); check("flip b", eq(flip(b), x(1, 2, const(1))))
check("flip c", eq(flip(c), x(3, 1, mono(-1, 1))))  # c -> c^-1
# 4. Cartan action: rotation and flip on diag entries (d1,d2,d3)
hA, hB = (1, -1, 0), (0, 1, -1)
rotd = lambda h: (h[1], h[2], h[0])        # rot: E11->E33, E22->E11, E33->E22
flipd = lambda h: (-h[2], -h[1], -h[0])    # -J X^T J^-1 on diagonals
hC = (-1, 0, 1)
check("rot hA", rotd(hA) == hC); check("rot hB", rotd(hB) == hA); check("flip hA", flipd(hA) == hB)
# 5. Bruhat identity
for N in (1, 2, 3):
    s = mono(1, N); one_s = padd(const(1), s); i1s = pinv(one_s)
    lhs = diag(one_s, i1s, const(1))
    rhs = mmul(mmul(mmul(x(2, 1, [(-v) % p for v in pmul(s, i1s)]), a), x(2, 1, s)), x(1, 2, [(-v) % p for v in i1s]))
    check("bruhat N=%d" % N, eq(lhs, rhs))
# 6. characters (exponents of (al,be,ga)) of the vertex elements vs W_n (n,n,n)
verts = {"a": (1, 0, 0), "b": (0, 1, 0), "c": (0, 0, 1), "[a,b]": (1, 1, 0), "[b,c]": (0, 1, 1), "[c,a]": (1, 0, 1)}
for nm, e in verts.items():
    nontriv = any(pow(al, e[0], p) * pow(be, e[1], p) * pow(pow(al * be, p - 2, p), e[2], p) % p != 1
                  for al in range(1, p) for be in range(1, p))
    check("char " + nm, nontriv)
print("ALL OK" if ok else "FAILURES", "p=%d M=%d" % (p, M))
