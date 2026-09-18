#!/usr/bin/env python3
"""Turn an optimal atom support into an exact F_2-linear configuration and write it for verify_linear.py.

usage: exact_support.py target.txt support.json rep.json
  support.json from atom_bin_lp.py (atom indices in atom_gen.c's mixed radix, float weights).
Steps (exact arithmetic only after reading the support):
  1. decode each support atom (codeword j -> one vector or zero on its read blocks) and compute its rank vector h_a;
  2. find exact rational weights on the support: solve the (T) rows and sum w = 1 by Fraction Gaussian elimination,
     with free variables fixed to rationalised LP weights; require w >= 0;
  3. check (T) and compute Phi exactly for the combination;
  4. scale to integer multiplicities n_a (sum D), and write the direct sum: block g of x is bits g*D .. g*D+D-1,
     copy c of atom a uses bit g*D + c; codeword j of copy c is one row (or none) supported on its read blocks.
"""
import sys, json
from fractions import Fraction as Fr
from math import lcm


def load(path):
    with open(path) as f:
        m, r = map(int, f.readline().split())
        reads = []
        for _ in range(r):
            t = list(map(int, f.readline().split())); reads.append(t[1:])
        col = list(map(int, f.readline().split()))
        my0, mx1yF, myF = map(int, f.readline().split())
    return m, r, reads, col, my0, mx1yF, myF


def rank2(rows):
    basis = []
    for v in rows:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v); basis.sort(reverse=True)
    return len(basis)


def decode(a, r, reads):
    code = []
    for j in range(r):
        k = len(reads[j]); loc = a & ((1 << k) - 1); a >>= k
        code.append(sum(1 << reads[j][i] for i in range(k) if loc >> i & 1))
    return code


def hvec(m, r, code, N):
    h = []
    for S in range(N):
        keep = sum(1 << g for g in range(m) if not S >> g & 1)
        nx = m - bin(keep).count('1')
        h.append(nx + rank2([code[j] & keep for j in range(r) if S >> (m + j) & 1]))
    return h


def main():
    m, r, reads, col, my0, mx1yF, myF = load(sys.argv[1])
    N = 1 << (m + r)
    sup = json.load(open(sys.argv[2]))['support']
    codes = [decode(a, r, reads) for a, _ in sup]
    H = [hvec(m, r, cd, N) for cd in codes]
    rep = {}
    for S in range(N):
        rep.setdefault(col[S], S)
    rows = []
    for S in range(N):
        if rep[col[S]] != S:
            row = [Fr(H[i][S] - H[i][rep[col[S]]]) for i in range(len(sup))]
            if any(row):
                rows.append(row + [Fr(0)])
    rows.append([Fr(1)] * len(sup) + [Fr(1)])
    n = len(sup)
    # row reduce
    piv = []; R = [row[:] for row in rows]; ri = 0
    for cidx in range(n):
        p = next((i for i in range(ri, len(R)) if R[i][cidx] != 0), None)
        if p is None:
            continue
        R[ri], R[p] = R[p], R[ri]
        inv = 1 / R[ri][cidx]; R[ri] = [v * inv for v in R[ri]]
        for i in range(len(R)):
            if i != ri and R[i][cidx] != 0:
                fac = R[i][cidx]; R[i] = [a - fac * b for a, b in zip(R[i], R[ri])]
        piv.append(cidx); ri += 1
    assert all(all(v == 0 for v in R[i]) for i in range(ri, len(R))), 'inconsistent'
    free = [cidx for cidx in range(n) if cidx not in piv]
    w = [None] * n
    for cidx in free:
        w[cidx] = Fr(sup[cidx][1]).limit_denominator(10000)
    for i, cidx in enumerate(piv):
        w[cidx] = R[i][n] - sum(R[i][fc] * w[fc] for fc in free)
    assert all(v >= 0 for v in w), 'negative weight'
    assert sum(w) == 1
    h = [sum(w[i] * H[i][S] for i in range(n)) for S in range(N)]
    assert all(h[S] == h[rep[col[S]]] for S in range(N)), '(T) fails'
    phi = h[my0] + h[mx1yF] - h[myF]
    D = 1
    for v in w:
        D = lcm(D, v.denominator)
    mult = [int(v * D) for v in w]
    W = [[] for _ in range(r)]
    c = 0
    for i in range(n):
        for _ in range(mult[i]):
            for j in range(r):
                v = codes[i][j]
                if v:
                    W[j].append(hex(sum(1 << (g * D + c) for g in range(m) if v >> g & 1)))
            c += 1
    assert c == D
    json.dump(dict(d=D, W=W, phi=str(phi), weights=[str(v) for v in w]), open(sys.argv[3], 'w'))
    print('support', n, 'D', D, 'exact phi', phi, 'rows per codeword', [len(x) for x in W])


if __name__ == '__main__':
    main()
