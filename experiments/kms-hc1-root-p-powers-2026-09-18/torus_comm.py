#!/usr/bin/env python3
"""Check the matrix input of lemma (RP) of kms-hc1-root-p-powers-die-first-deviation-at-3np.

Work in SL_3(F_p[t]/t^N).  The six vertex elements of Gamma^A2_p map to
  a -> x12(1), b -> x23(1), c -> x31(t), [a,b], [b,c], [c,a]   ([x,y] = x^-1 y^-1 x y).
For each vertex element x (image in the root group X_beta, t-valuation k0) and each m >= 1,
take the torus element s = diag(..,1+t^m at i,..,(1+t^m)^-1 at j,..) for beta = e_i - e_j, and check:
  (1) x^p = 1;
  (2) g = [x, s] lies in the root group X_beta, with t-valuation k0+m and a unit leading coefficient;
  (3) [g, x] = 1 and x g = s^-1 x s;
  (4) every positive real affine root of degree <= H arises exactly once as (x, m), m >= 0,
      with degree deg(t^k E_ij) = 3k + j - i.
usage: torus_comm.py p N H
"""
import sys
p, N, H = (int(v) for v in sys.argv[1:4])

def smul(f, g):
    r = [0] * N
    for i, x in enumerate(f):
        if x:
            for j in range(N - i):
                r[i + j] = (r[i + j] + x * g[j]) % p
    return r

def sadd(f, g): return [(x + y) % p for x, y in zip(f, g)]
def sconst(c, k=0):
    r = [0] * N
    if k < N: r[k] = c % p
    return r
def sinv(f):  # f[0] != 0
    i0 = pow(f[0], p - 2, p); r = [0] * N; r[0] = i0
    for n in range(1, N):
        s = sum(f[k] * r[n - k] for k in range(1, n + 1)) % p
        r[n] = (-s * i0) % p
    return r

Z = [0] * N
def mmul(A, B):
    return [[sadd(sadd(smul(A[i][0], B[0][j]), smul(A[i][1], B[1][j])), smul(A[i][2], B[2][j]))
             for j in range(3)] for i in range(3)]
def ident(): return [[sconst(1 if i == j else 0) for j in range(3)] for i in range(3)]
def elem(i, j, f):
    M = ident(); M[i][j] = sadd(M[i][j], f); return M
def minv_unip_or_torus(M):  # inverse via adjugate (det = 1)
    def cof(i, j):
        r = [x for x in range(3) if x != i]; c = [y for y in range(3) if y != j]
        d = sadd(smul(M[r[0]][c[0]], M[r[1]][c[1]]), [(-v) % p for v in smul(M[r[0]][c[1]], M[r[1]][c[0]])])
        return d if (i + j) % 2 == 0 else [(-v) % p for v in d]
    return [[cof(j, i) for j in range(3)] for i in range(3)]
def comm(x, y): return mmul(mmul(minv_unip_or_torus(x), minv_unip_or_torus(y)), mmul(x, y))
def mpow(M, e):
    R = ident()
    for _ in range(e): R = mmul(R, M)
    return R
def is_id(M): return M == ident()

t1 = sconst(1, 1)
a, b, c = elem(0, 1, sconst(1)), elem(1, 2, sconst(1)), elem(2, 0, t1)
verts = {'a': a, 'b': b, 'c': c, '[a,b]': comm(a, b), '[b,c]': comm(b, c), '[c,a]': comm(c, a)}

def root_of(M):  # returns (i,j,f) if M = x_ij(f), else None
    off = [(i, j) for i in range(3) for j in range(3) if i != j and any(M[i][j])]
    D = ident()
    if len(off) != 1 or any(M[i][i] != D[i][i] for i in range(3)): return None
    i, j = off[0]; return i, j, M[i][j]
def val(f): return next(k for k, x in enumerate(f) if x)

ok = True; seen = {}
for name, x in verts.items():
    i, j, f = root_of(x); k0 = val(f)
    if not is_id(mpow(x, p)): ok = False; print('FAIL x^p', name)
    deg0 = 3 * k0 + j - i
    seen.setdefault((i, j, k0), []).append((name, 0))
    for m in range(1, (H - deg0) // 3 + 1):
        u = sadd(sconst(1), sconst(1, m)); s = ident(); s[i][i] = u; s[j][j] = sinv(u)
        g = comm(x, s); rg = root_of(g)
        if rg is None or rg[:2] != (i, j): ok = False; print('FAIL root group', name, m); continue
        k = val(rg[2]); lead = rg[2][k]
        good = (k == k0 + m) and lead % p != 0 and is_id(comm(g, x)) and \
               mmul(x, g) == mmul(mmul(minv_unip_or_torus(s), x), s)
        if not good: ok = False
        seen.setdefault((i, j, k), []).append((name, m))
        print(f'{name:6s} beta=e{i+1}-e{j+1} m={m}: g = x{i+1}{j+1}({lead}*t^{k}+...) '
              f'degree {3*k+j-i}  [g,x]=1 and xg=x^s: {good}')
# every positive real affine root of degree 1..H exactly once
for i in range(3):
    for j in range(3):
        if i == j: continue
        for k in range(0, H):
            d = 3 * k + j - i
            if 1 <= d <= H and len(seen.get((i, j, k), [])) != 1:
                ok = False; print('FAIL coverage', i + 1, j + 1, k, seen.get((i, j, k)))
print(f'p={p} N={N} degrees<={H}: ALL OK' if ok else f'p={p}: FAILURES')
