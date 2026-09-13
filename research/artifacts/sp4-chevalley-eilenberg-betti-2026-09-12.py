#!/usr/bin/env python3
# Chevalley--Eilenberg Betti numbers b1,b2,b3 with trivial coefficients over Q.
# Calibration: abelian Q^2 (b2=1), heis (2,2,1), sl2 (0,0,1); target sp4 (0,0,1).
from fractions import Fraction
from itertools import combinations

def rank(rows):
    M = [list(map(Fraction, r)) for r in rows]
    r = 0
    ncol = len(M[0]) if M else 0
    for c in range(ncol):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c] / M[r][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
    return r

def sort_sign(t):
    t = list(t)
    if len(set(t)) < len(t):
        return 0, None
    s = 1
    for i in range(len(t)):
        for j in range(len(t) - 1 - i):
            if t[j] > t[j + 1]:
                t[j], t[j + 1] = t[j + 1], t[j]
                s = -s
    return s, tuple(t)

def d_matrix(n, C, k):
    # d: Lambda^k g* -> Lambda^{k+1} g*; rows indexed by (k+1)-tuples T, cols by k-tuples S
    Ks = list(combinations(range(n), k))
    idx = {S: i for i, S in enumerate(Ks)}
    rows = []
    for T in combinations(range(n), k + 1):
        row = [0] * len(Ks)
        for i, j in combinations(range(k + 1), 2):
            rest = [T[m] for m in range(k + 1) if m not in (i, j)]
            for c, v in C.get((T[i], T[j]), {}).items():
                s, S = sort_sign([c] + rest)
                if s:
                    row[idx[S]] += (-1) ** (i + j) * s * v
        rows.append(row)
    return rows

def betti(n, C):
    r = {0: 0}
    for k in (1, 2, 3):
        r[k] = rank(d_matrix(n, C, k))
    from math import comb
    return tuple(comb(n, k) - r[k] - r[k - 1] for k in (1, 2, 3))

def from_matrices(basis, coords):
    n = len(basis)
    def mul(A, B):
        m = len(A)
        return [[sum(A[i][l] * B[l][j] for l in range(m)) for j in range(m)] for i in range(m)]
    C = {}
    for a in range(n):
        for b in range(n):
            AB, BA = mul(basis[a], basis[b]), mul(basis[b], basis[a])
            br = [[AB[i][j] - BA[i][j] for j in range(len(AB))] for i in range(len(AB))]
            co = coords(br)
            C[(a, b)] = {c: v for c, v in enumerate(co) if v != 0}
    return n, C

def E(m, i, j):
    M = [[0] * m for _ in range(m)]
    M[i][j] = 1
    return M

def sl2():
    b = [[[0, 1], [0, 0]], [[0, 0], [1, 0]], [[1, 0], [0, -1]]]
    return from_matrices(b, lambda X: [X[0][1], X[1][0], X[0][0]])

def sp4():
    b = []
    for i in range(2):
        for j in range(2):  # [[A,0],[0,-A^T]]
            M = E(4, i, j)
            M[2 + j][2 + i] -= 1
            b.append(M)
    for (i, j) in ((0, 0), (1, 1), (0, 1)):  # B symmetric, C symmetric
        M = E(4, i, 2 + j)
        if i != j:
            M[j][2 + i] += 1
        b.append(M)
    for (i, j) in ((0, 0), (1, 1), (0, 1)):
        M = E(4, 2 + i, j)
        if i != j:
            M[2 + j][i] += 1
        b.append(M)
    coords = lambda X: [X[0][0], X[0][1], X[1][0], X[1][1], X[0][2], X[1][3], X[0][3],
                        X[2][0], X[3][1], X[2][1]]
    for M in b:  # symplectic check X^T J + J X = 0 and coordinates round-trip
        J = [[0, 0, 1, 0], [0, 0, 0, 1], [-1, 0, 0, 0], [0, -1, 0, 0]]
        XT = [[M[j][i] for j in range(4)] for i in range(4)]
        s = [[sum(XT[i][l] * J[l][j] + J[i][l] * M[l][j] for l in range(4)) for j in range(4)] for i in range(4)]
        assert all(v == 0 for r in s for v in r)
    return from_matrices(b, coords)

print("abelian2", betti(2, {}))
print("heis", betti(3, {(0, 1): {2: 1}, (1, 0): {2: -1}}))
print("sl2", betti(*sl2()))
print("sp4", betti(*sp4()))
print("DONE")
