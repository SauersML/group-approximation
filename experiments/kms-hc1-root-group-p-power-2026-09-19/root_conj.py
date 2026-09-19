#!/usr/bin/env python3
"""Checks for kms-hc1-p-power-value-vanishes-on-affine-root-groups.

Matrices over F_p[t]/t^N (series truncated at t^N). Usage: root_conj.py p N.
 (1) vertex images: [a,b], [b,c], [c,a] are root elements x13, x21(t), x32(t)
     up to sign, and all generators and commutators have order p;
 (2) for every root (i,j), random f in the allowed ideal: x_ij(f) is either
     Ad(d) of a vertex root element x_ij(lam t^v0) with d diagonal in I_1,
     or the product of two commuting such elements;
 (3) content invariant: no conjugate of a vertex element by B^+(F_p) mod t
     has reduced leading term (g-1)/t = E13, E12 or E23 (so x13(t), x12(t),
     x23(t) are not I_1-conjugate into a vertex group); and x21(t^n), n>=2,
     has content (t^n), not (1) or (t).
"""
import sys, random, itertools
p, N = int(sys.argv[1]), int(sys.argv[2])
random.seed(p * 1000 + N)

def sadd(f, g): return [(x + y) % p for x, y in zip(f, g)]
def smul(f, g):
    h = [0] * N
    for i, x in enumerate(f):
        if x:
            for j in range(N - i):
                h[i + j] = (h[i + j] + x * g[j]) % p
    return h
def sinv(f):  # f(0) != 0
    inv0 = pow(f[0], p - 2, p); g = [0] * N; g[0] = inv0
    for k in range(1, N):
        s = sum(f[i] * g[k - i] for i in range(1, k + 1)) % p
        g[k] = (-s * inv0) % p
    return g
def ssqrt(u):  # u(0) = 1
    g = [0] * N; g[0] = 1
    for k in range(1, N):
        s = sum(g[i] * g[k - i] for i in range(1, k)) % p
        g[k] = ((u[k] - s) * pow(2, p - 2, p)) % p
    return g
def sc(c): return [c % p] + [0] * (N - 1)
def tp(k, c=1): v = [0] * N; v[k] = c % p; return v
Z = [0] * N
def mmul(A, B):
    return [[sadd(sadd(smul(A[i][0], B[0][j]), smul(A[i][1], B[1][j])),
                  smul(A[i][2], B[2][j])) for j in range(3)] for i in range(3)]
def I3(): return [[sc(1) if i == j else Z[:] for j in range(3)] for i in range(3)]
def x(i, j, f): M = I3(); M[i][j] = f; return M
def diag(d): M = I3(); [M[k].__setitem__(k, d[k]) for k in range(3)]; return M
def minv_unip(M):  # inverse of unipotent-type matrix via adjugate (det 1 assumed)
    def c(i, j):
        r = [k for k in range(3) if k != i]; s = [k for k in range(3) if k != j]
        a = sadd(smul(M[r[0]][s[0]], M[r[1]][s[1]]),
                 [(-v) % p for v in smul(M[r[0]][s[1]], M[r[1]][s[0]])])
        return a if (i + j) % 2 == 0 else [(-v) % p for v in a]
    return [[c(j, i) for j in range(3)] for i in range(3)]
def comm(A, B): return mmul(mmul(minv_unip(A), minv_unip(B)), mmul(A, B))
def mpow(A, k):
    R = I3()
    for _ in range(k): R = mmul(R, A)
    return R
def eq(A, B): return A == B
a, b, c = x(0, 1, sc(1)), x(1, 2, sc(1)), x(2, 0, tp(1))
ok = True
# (1)
for name, g in [('a', a), ('b', b), ('c', c), ('[a,b]', comm(a, b)),
                ('[b,c]', comm(b, c)), ('[c,a]', comm(c, a))]:
    if not eq(mpow(g, p), I3()): ok = False; print('order fail', name)
for name, g, (i, j, v) in [('[a,b]', comm(a, b), (0, 2, 0)),
                           ('[b,c]', comm(b, c), (1, 0, 1)),
                           ('[c,a]', comm(c, a), (2, 1, 1))]:
    lam = g[i][j][v]
    if lam == 0 or not eq(g, x(i, j, tp(v, lam))): ok = False; print('root fail', name)
    else: print(name, '= x_%d%d(%d t^%d)' % (i + 1, j + 1, lam, v))
# (2)
roots = [(0, 1, 0), (1, 2, 0), (0, 2, 0), (1, 0, 1), (2, 1, 1), (2, 0, 1)]
def ratio_diag(i, j, u):  # diagonal d in I_1 with d_i/d_j = u
    r = ssqrt(u); d = [sc(1)] * 3; k = 3 - i - j
    d = [None] * 3; d[i] = r; d[j] = sinv(r); d[k] = sc(1)
    return diag(d)
trials = 0
for (i, j, v0) in roots:
    for _ in range(40):
        g = [random.randrange(p) for _ in range(N - v0)]
        if random.random() < 0.5: g[0] = 0
        f = [0] * v0 + g
        lam = g[0]
        if lam:
            u = smul(tp(0, 1), [0] * 0 + [(gg * pow(lam, p - 2, p)) % p for gg in g] + [0] * v0)
            d = ratio_diag(i, j, u)
            y = mmul(mmul(d, x(i, j, tp(v0, lam))), diag([sinv(d[k][k]) for k in range(3)]))
            if not eq(y, x(i, j, f)): ok = False; print('conj fail', i, j)
        else:
            u = sadd(sc(1), g + [0] * v0)
            d = ratio_diag(i, j, u)
            y1 = mmul(mmul(d, x(i, j, tp(v0, 1))), diag([sinv(d[k][k]) for k in range(3)]))
            y2 = x(i, j, tp(v0, -1))
            if not (eq(mmul(y1, y2), x(i, j, f)) and eq(mmul(y1, y2), mmul(y2, y1))):
                ok = False; print('prod fail', i, j)
        trials += 1
print('root-group decompositions checked:', trials)
# (3) leading terms of content-(t) vertex elements, conjugated by B^+(F_p)
def mat(e): return [[e.get((r, s), 0) % p for s in range(3)] for r in range(3)]
def mm(A, B): return [[sum(A[r][k] * B[k][s] for k in range(3)) % p for s in range(3)] for r in range(3)]
lead = set()
for v, w in itertools.product(range(p), repeat=2):
    for N0 in (mat({(2, 0): v, (1, 0): w}), mat({(2, 0): v, (2, 1): w})):
        for u12, u13, u23 in itertools.product(range(p), repeat=3):
            U = mat({(0, 0): 1, (1, 1): 1, (2, 2): 1, (0, 1): u12, (0, 2): u13, (1, 2): u23})
            Ui = mat({(0, 0): 1, (1, 1): 1, (2, 2): 1, (0, 1): -u12,
                      (0, 2): u12 * u23 - u13, (1, 2): -u23})
            lead.add(tuple(map(tuple, mm(mm(U, N0), Ui))))
for (i, j) in [(0, 2), (0, 1), (1, 2)]:
    if tuple(map(tuple, mat({(i, j): 1}))) in lead: ok = False; print('E%d%d reached' % (i + 1, j + 1))
print('leading terms reachable from content-(t) vertex elements:', len(lead))
print('ALL OK' if ok else 'FAILURES')
# (4) SL_2 Bruhat identity behind the Cartan relator (block 12):
#     x12(u) x21(s) = x21(s/(1+us)) h(1+us) x12(u/(1+us)),  h(v) = diag(v, 1/v, 1)
for n in range(1, 4):
    u, s = sc(1), tp(n)
    w = sadd(sc(1), smul(u, s)); wi = sinv(w)
    lhs = mmul(x(0, 1, u), x(1, 0, s))
    rhs = mmul(mmul(x(1, 0, smul(s, wi)), diag([w, wi, sc(1)])), x(0, 1, smul(u, wi)))
    hp = mpow(diag([w, wi, sc(1)]), p)
    wp = sadd(sc(1), tp(n * p)) if n * p < N else sc(1)
    print('n=%d Bruhat identity' % n, eq(lhs, rhs), ' h(1+t^n)^p = h(1+t^np):',
          eq(hp, diag([wp, sinv(wp), sc(1)])))
