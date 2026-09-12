#!/usr/bin/env python3
# kh-cckw: verify the EXACT readout formulas and decide-certificates used in Kazhdan/GHBQuotientVertexForms.lean.
import itertools
p = 7; n = 4
def mul(A, B): return tuple(tuple(sum(A[i][t]*B[t][j] for t in range(n)) % p for j in range(n)) for i in range(n))
I = tuple(tuple(int(i == j) for j in range(n)) for i in range(n))
def E(entries):
    M = [list(r) for r in I]
    for (r, c), v in entries.items(): M[r][c] = (M[r][c] + v) % p
    return tuple(tuple(r) for r in M)
A = E({(0,3):1, (1,2):1}); B = E({(1,0):1, (2,3):-1}); C = E({(3,1):1})
Ai = E({(0,3):-1, (1,2):-1}); Bi = E({(1,0):-1, (2,3):1}); Ci = E({(3,1):-1})
INV = {A: Ai, B: Bi, C: Ci}
def pw(X, e):
    R = I
    for _ in range(e): R = mul(R, X)
    return R
def inv(X):
    if X in INV: return INV[X]
    R = I; Bq = X; e = 7**4 - 1
    while e:
        if e & 1: R = mul(R, Bq)
        Bq = mul(Bq, Bq); e >>= 1
    return R
def comm(x, y): return mul(mul(mul(inv(x), inv(y)), x), y)
AB = comm(A, B); CB = comm(C, B); CBB = comm(CB, B); CA = comm(C, A); CAA = comm(CA, A)
def wordAB(t): return mul(mul(pw(A,t[0]), pw(B,t[1])), pw(AB,t[2]))
def readAB(M): return (M[0][3], M[1][0], (4 * (-M[1][3] - M[0][3]*M[1][0])) % p)
def wordCB(t): return mul(mul(mul(pw(C,t[0]), pw(B,t[1])), pw(CB,t[2])), pw(CBB,t[3]))
def readCB(M): return (M[3][1], M[1][0], M[2][1], (4 * (M[2][0] - M[2][1] + M[1][0]*M[2][1])) % p)
def wordCA(t): return mul(mul(mul(pw(C,t[0]), pw(A,t[1])), pw(CA,t[2])), pw(CAA,t[3]))
def readCA(M): return (M[3][1], M[0][3], (6*M[0][1]) % p, (3 * (M[0][2] + 6*M[0][1] - M[0][3]*(6*M[0][1]))) % p)
for name, word, read, gens, arity in [("AB", wordAB, readAB, [A, B], 3), ("CB", wordCB, readCB, [C, B], 4), ("CA", wordCA, readCA, [C, A], 4)]:
    ts = list(itertools.product(range(7), repeat=arity))
    r1 = all(read(word(t)) == t for t in ts)
    r2 = all(word(read(mul(g, word(t)))) == mul(g, word(t)) for g in gens + [inv(g) for g in gens] for t in ts)
    r3 = all(pw(word(t), 7) == I for t in ts)
    print(name, "readout:", r1, " left-mult closure (g, g^-1):", r2, " exponent 7:", r3, " word(0)=I:", word(tuple([0]*arity)) == I)
print("(A B C)^7 != I:", pw(mul(mul(A, B), C), 7) != I)
