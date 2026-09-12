#!/usr/bin/env python3
# kh-cckw: model test of the parameter families used in Kazhdan/GHBQuotientVertexFamilies.lean.
import itertools
p = 7; n = 4
def mul(A, B): return tuple(tuple(sum(A[i][t]*B[t][j] for t in range(n)) % p for j in range(n)) for i in range(n))
I = tuple(tuple(int(i == j) for j in range(n)) for i in range(n))
def M(rows): return tuple(tuple(v % p for v in r) for r in rows)
A = M([[1,0,0,1],[0,1,1,0],[0,0,1,0],[0,0,0,1]]); Ai = M([[1,0,0,6],[0,1,6,0],[0,0,1,0],[0,0,0,1]])
B = M([[1,0,0,0],[1,1,0,0],[0,0,1,6],[0,0,0,1]]); Bi = M([[1,0,0,0],[6,1,0,0],[0,0,1,1],[0,0,0,1]])
C = M([[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,1,0,1]]); Ci = M([[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,6,0,1]])
INV = {A: Ai, B: Bi, C: Ci}
def inv(X):
    if X in INV: return INV[X]
    R = I; Bq = X; e = 7**4 - 1
    while e:
        if e & 1: R = mul(R, Bq)
        Bq = mul(Bq, Bq); e >>= 1
    return R
def pw(X, e):
    R = I
    for _ in range(e): R = mul(R, X)
    return R
def comm(x, y): return mul(mul(mul(inv(x), inv(y)), x), y)
def comm3(x, y, z): return comm(comm(x, y), z)
def matAB(t): i, j, x = t; return M([[1,0,0,i],[j,1,i,x],[0,0,1,-j],[0,0,0,1]])
def mulAB(s, t): return ((s[0]+t[0]) % p, (s[1]+t[1]) % p, (s[2]+t[2]+s[1]*t[0]-s[0]*t[1]) % p)
def matCB(t): i, j, k, u = t; return M([[1,0,0,0],[j,1,0,0],[u,k,1,-j],[k+i*j,i,0,1]])
def mulCB(s, t): return ((s[0]+t[0]) % p, (s[1]+t[1]) % p, (s[2]+t[2]-s[1]*t[0]) % p, (s[3]+t[3]+s[2]*t[1]-s[1]*(t[2]+t[0]*t[1])) % p)
def matCA(t): i, j, k, w = t; return M([[1,-k,w,j],[0,1,j,0],[0,0,1,0],[0,i,k+i*j,1]])
def mulCA(s, t): return ((s[0]+t[0]) % p, (s[1]+t[1]) % p, (s[2]+t[2]-s[1]*t[0]) % p, (s[3]+t[3]-s[2]*t[1]+s[1]*(t[2]+t[0]*t[1])) % p)
def powX(mulX, zero, t, e):
    r = zero
    for _ in range(e): r = mulX(r, t)
    return r
import random
rng = random.Random(1)
P3 = list(itertools.product(range(7), repeat=3)); P4 = list(itertools.product(range(7), repeat=4))
okAB = all(mul(matAB(s), matAB(t)) == matAB(mulAB(s, t)) for s in P3 for t in P3)
okCB = all(mul(matCB(s), matCB(t)) == matCB(mulCB(s, t)) for s in rng.sample(P4, 400) for t in rng.sample(P4, 400))
okCA = all(mul(matCA(s), matCA(t)) == matCA(mulCA(s, t)) for s in rng.sample(P4, 400) for t in rng.sample(P4, 400))
print("laws AB (all pairs):", okAB, " CB (160k pairs):", okCB, " CA (160k pairs):", okCA)
print("zero:", matAB((0,0,0)) == I, matCB((0,0,0,0)) == I, matCA((0,0,0,0)) == I)
print("gens AB:", A == matAB((1,0,0)), Ai == matAB((6,0,0)), B == matAB((0,1,0)), Bi == matAB((0,6,0)))
print("gens CB:", C == matCB((1,0,0,0)), Ci == matCB((6,0,0,0)), B == matCB((0,1,0,0)), Bi == matCB((0,6,0,0)))
print("gens CA:", C == matCA((1,0,0,0)), Ci == matCA((6,0,0,0)), A == matCA((0,1,0,0)), Ai == matCA((0,6,0,0)))
print("zAB = [a,b]^3:", pw(comm(A, B), 3) == matAB((0,0,1)))
print("dCB = [c,b]:", comm(C, B) == matCB((0,0,1,1)), " eCB = [c,b,b]^4:", pw(comm3(C, B, B), 4) == matCB((0,0,0,1)))
print("dCA = [c,a]:", comm(C, A) == matCA((0,0,1,6)), " eCA = [c,a,a]^3:", pw(comm3(C, A, A), 3) == matCA((0,0,0,1)))
print("pow7 AB:", all(powX(mulAB, (0,0,0), t, 7) == (0,0,0) for t in P3),
      " CB:", all(powX(mulCB, (0,0,0,0), t, 7) == (0,0,0,0) for t in P4),
      " CA:", all(powX(mulCA, (0,0,0,0), t, 7) == (0,0,0,0) for t in P4))
wAB = all(mulAB(mulAB(powX(mulAB,(0,0,0),(1,0,0),i), powX(mulAB,(0,0,0),(0,1,0),j)), powX(mulAB,(0,0,0),(0,0,1),(x+i*j) % p)) == (i,j,x) for (i,j,x) in P3)
wCB = all(mulCB(mulCB(mulCB(powX(mulCB,(0,)*4,(1,0,0,0),i), powX(mulCB,(0,)*4,(0,1,0,0),j)), powX(mulCB,(0,)*4,(0,0,1,1),k)), powX(mulCB,(0,)*4,(0,0,0,1),(u-k+j*k) % p)) == (i,j,k,u) for (i,j,k,u) in P4)
wCA = all(mulCA(mulCA(mulCA(powX(mulCA,(0,)*4,(1,0,0,0),i), powX(mulCA,(0,)*4,(0,1,0,0),j)), powX(mulCA,(0,)*4,(0,0,1,6),k)), powX(mulCA,(0,)*4,(0,0,0,1),(w-6*k-j*k) % p)) == (i,j,k,w) for (i,j,k,w) in P4)
print("words AB:", wAB, " CB:", wCB, " CA:", wCA)
