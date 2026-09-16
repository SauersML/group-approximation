#!/usr/bin/env python3
# Chevalley--Eilenberg Betti numbers b1,b2,b3 with trivial coefficients over Q.
# Adapted 2026-09-16 from research/artifacts/sp4-chevalley-eilenberg-betti-2026-09-12.py.
# Calibration: abelian Q^2 (2,1,0), heis (2,2,1), sl2 (0,0,1); targets sl3 and gl3.
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

def sl3():
    offd = [(i, j) for i in range(3) for j in range(3) if i != j]
    b = [E(3, i, j) for (i, j) in offd]
    h1 = E(3, 0, 0); h1[1][1] = -1
    h2 = E(3, 1, 1); h2[2][2] = -1
    b += [h1, h2]
    # traceless X = sum x_ij E_ij + a h1 + b h2 with a = X[0][0], b = -X[2][2]
    coords = lambda X: [X[i][j] for (i, j) in offd] + [X[0][0], -X[2][2]]
    for M in b:
        assert sum(M[i][i] for i in range(3)) == 0
        co = coords(M)
        R = [[0] * 3 for _ in range(3)]
        for c, (i, j) in enumerate(offd):
            R[i][j] += co[c]
        for c, H in ((6, h1), (7, h2)):
            for i in range(3):
                R[i][i] += co[c] * H[i][i]
        assert R == M
    return from_matrices(b, coords)

def gl3():
    b = [E(3, i, j) for i in range(3) for j in range(3)]
    return from_matrices(b, lambda X: [X[i][j] for i in range(3) for j in range(3)])

print("abelian2", betti(2, {}))
print("heis", betti(3, {(0, 1): {2: 1}, (1, 0): {2: -1}}))
print("sl2", betti(*sl2()))
print("sl3", betti(*sl3()))
print("gl3", betti(*gl3()))
print("DONE")
