#!/usr/bin/env python3
"""Search natural GL_n(2) completions of the two shortest Jacobson cells.

The head GL3(2) acts on coordinates 0,1,2 and fixes the auxiliary
coordinates.  K=GL(<e0,e2>) fixes e1, so a K-central involution h is the
identity on e0,e2 and an arbitrary involution H on the trivial space spanned
by e1 and the auxiliary coordinates.
"""

from itertools import product


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def mul(a, b):
    n = len(a)
    return [[sum(a[i][k] * b[k][j] for k in range(n)) & 1
             for j in range(n)] for i in range(n)]


def power(a, k):
    out = eye(len(a))
    for _ in range(k):
        out = mul(out, a)
    return out


def rank(a):
    a = [row[:] for row in a]
    n = len(a)
    pivot = 0
    for col in range(n):
        hit = next((i for i in range(pivot, n) if a[i][col]), None)
        if hit is None:
            continue
        a[pivot], a[hit] = a[hit], a[pivot]
        for i in range(n):
            if i != pivot and a[i][col]:
                a[i] = [x ^ y for x, y in zip(a[i], a[pivot])]
        pivot += 1
    return pivot


def perm(n, cycle):
    p = list(range(n))
    for i, j in zip(cycle, cycle[1:] + cycle[:1]):
        p[i] = j
    # Column vectors: matrix sends e_i to e_{p[i]}.
    out = [[0] * n for _ in range(n)]
    for i, j in enumerate(p):
        out[j][i] = 1
    return out


def transpose(a):
    return [list(row) for row in zip(*a)]


def matrices(t):
    for bits in range(1 << (t * t)):
        yield [[(bits >> (i * t + j)) & 1 for j in range(t)]
               for i in range(t)]


def search(t):
    n = t + 2
    trivial = [1] + list(range(3, n))
    u12 = perm(n, [0, 1])
    r23 = perm(n, [1, 2])
    cyc = perm(n, [0, 1, 2])
    cyc_inv = transpose(cyc)
    cyc2 = mul(cyc, cyc)
    cyc2_inv = transpose(cyc2)
    identity = eye(n)
    tested = 0
    braid = 0
    joint = []
    for small in matrices(t):
        if rank(small) != t or mul(small, small) != eye(t):
            continue
        tested += 1
        h = eye(n)
        for i, ii in enumerate(trivial):
            for j, jj in enumerate(trivial):
                h[ii][jj] = small[i][j]
        if power(mul(h, r23), 3) != identity:
            continue
        braid += 1
        a12 = mul(h, u12)
        a23 = mul(mul(cyc, a12), cyc_inv)
        a31 = mul(mul(cyc2, a12), cyc2_inv)
        if mul(mul(a31, a23), a12) == r23:
            joint.append(small)
    print({"trivial_dimension": t, "ambient_dimension": n,
           "involutions_tested": tested, "braid_solutions": braid,
           "joint_solutions": len(joint)})
    for solution in joint[:3]:
        print(solution)


for trivial_dimension in (1, 2, 3, 4):
    search(trivial_dimension)
