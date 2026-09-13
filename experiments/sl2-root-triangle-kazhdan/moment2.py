# moment2.py -- first-level edge-twist moment test (p = 2, elementary abelian edge groups) for the untwisted
# Kazhdan SL_2 root triangle Lambda_0, through rho: Lambda_0 -> Q = SL_2(q^2) of
# sl2-root-kazhdan-triangle-untwisted-member-maps-onto-sl2. N = ker rho is torsion-free.
#   images of the edge groups:  E_12 = { h u(x) h^-1 } = {[[1+Px, P^2 x],[x, 1+Px]]},  E_13 = u(k),  E_23 = v(sk)
#   B      = right-coset indicator rows (3|Q|/q rows, |Q| columns) = boundary map of N\X over F_2
#   dim Z_N = |Q| - rank B = b_2(N;F_2),   b_1(N;F_2) = 1 + b_2 - chi(N\X)
#   moments: for a twist c_e in Hom(E_e,F_2), mu(lambda) = sum over cosets sum_{x in E_e} c_e(x) lambda(x q_0);
#   dim I_N = rank([B; moment rows]) - rank B  (moment rows use all n bit functionals of the parameter)
# Usage: sage -python moment2.py n f s_exp
import sys, time
import numpy as np
from sage.all import GF, matrix

def field(n):
    N = 1 << n
    for poly in range(N + 1, 2 * N, 2):
        exp = np.zeros(2 * N, dtype=np.int64); x = 1; seen = set(); ok = True
        for i in range(N - 1):
            if x in seen: ok = False; break
            seen.add(x); exp[i] = x
            x <<= 1
            if x & N: x ^= poly
        if ok and x == 1 and len(seen) == N - 1:
            exp[N - 1:2 * N - 1] = exp[0:N]
            log = np.zeros(N, dtype=np.int64); log[exp[:N - 1]] = np.arange(N - 1)
            return poly, exp, log
    raise ValueError

n, f, s_exp = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
N = 1 << n; q = 1 << f
poly, EXP, LOG = field(n)
def mul(a, b):
    a = np.asarray(a, dtype=np.int64); b = np.asarray(b, dtype=np.int64)
    return np.where((a == 0) | (b == 0), 0, EXP[LOG[a] + LOG[b]])
def powi(a, e):
    return 0 if a == 0 else int(EXP[(LOG[a] * e) % (N - 1)])
k = [a for a in range(N) if powi(a, q) == a]
s = int(EXP[s_exp]); assert s not in k
P = powi(powi(s, N - 2), N // 2)                       # P = s^(-1/2)
assert int(mul(mul(P, P), s)) == 1
t0 = time.time()
# enumerate SL_2(F_N)
a, b, c, d = np.meshgrid(np.arange(N), np.arange(N), np.arange(N), np.arange(N), indexing="ij")
a, b, c, d = a.ravel(), b.ravel(), c.ravel(), d.ravel()
sel = (mul(a, d) ^ mul(b, c)) == 1
a, b, c, d = a[sel], b[sel], c[sel], d[sel]
nQ = len(a); assert nQ == N * (N * N - 1)
code = ((a * N + b) * N + c) * N + d
index = -np.ones(N ** 4, dtype=np.int64); index[code] = np.arange(nQ)
def left(x, a, b, c, d):                                  # x * g for a 2x2 matrix x = (x11,x12,x21,x22)
    x11, x12, x21, x22 = x
    return (mul(x11, a) ^ mul(x12, c), mul(x11, b) ^ mul(x12, d), mul(x21, a) ^ mul(x22, c), mul(x21, b) ^ mul(x22, d))
edges = {
    "12": [(1 ^ int(mul(P, x)), int(mul(mul(P, P), x)), x, 1 ^ int(mul(P, x))) for x in k],
    "13": [(1, x, 0, 1) for x in k],
    "23": [(1, 0, int(mul(s, x)), 1) for x in k],
}
rows = []                                                   # list of (list of column indices) for B
momrows = []
for e, mats in edges.items():
    prod = np.stack([index[(((lambda t: (t[0] * N + t[1]) * N + t[2])(left(x, a, b, c, d))) * N) + left(x, a, b, c, d)[3]] for x in mats])
    assert (prod >= 0).all()
    rep = prod.min(axis=0)                                  # canonical coset representative q_0 of E g
    which = prod.argmin(axis=0)                             # x* with x* g = q_0, so g = x* q_0 (x* is an involution)
    par = np.array(k)[which]                                # parameter of x*
    cos_ids, inv = np.unique(rep, return_inverse=True)
    assert len(cos_ids) == nQ // q
    order = np.argsort(inv, kind="stable")
    for grp in np.split(order, np.cumsum(np.bincount(inv))[:-1]):
        rows.append(grp)
    for bit in range(n):
        momrows.append(np.nonzero((par >> bit) & 1)[0])
print("N=%d q=%d |Q|=%d cosets=%d build %.1fs" % (N, q, nQ, len(rows), time.time() - t0), flush=True)
t0 = time.time()
Mx = matrix(GF(2), len(rows) + len(momrows), nQ)
for i, grp in enumerate(rows + momrows):
    for j in grp.tolist():
        Mx[i, j] = 1
print("matrix filled %.1fs" % (time.time() - t0), flush=True)
t0 = time.time()
rB = Mx.matrix_from_rows(range(len(rows))).rank()
print("rank B = %d (%.1fs)" % (rB, time.time() - t0), flush=True)
t0 = time.time()
rBM = Mx.rank()
print("rank [B;M] = %d (%.1fs)" % (rBM, time.time() - t0), flush=True)
nv = nQ // (q * (q * q - 1)) * 2 + 1
chi = nv - len(rows) + nQ
b2 = nQ - rB
print("vertices=%d edges=%d faces=%d chi=%d  b2(N;F_2)=%d  b1(N;F_2)=%d  dim I_N=%d (of %d)" % (nv, len(rows), nQ, chi, b2, 1 + b2 - chi, rBM - rB, 3 * f))
print("DONE")
