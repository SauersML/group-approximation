#!/usr/bin/env python3
"""Check the nested-commutator identity behind
research/sft-leavitt-units-word-problem-computes-sft-language.md.

Over F_2, for x = a*E_ij and y = b*E_jk with i, j, k distinct,
  [1 + x, 1 + y] = (1+x)(1+y)(1+x)^(-1)(1+y)^(-1) = 1 + ab*E_ik,
with a, b arbitrary (noncommuting) elements of a ring R. We model R = M_n(F_2)
(random, noncommuting, some idempotent), build the balanced commutator tree
over m leaves with index pairs chosen as in the proof, and check that the
result is 1 + (a_1 a_2 ... a_m) E_13. We also check the word-length recursion
len(m) = 2 len(ceil(m/2)) + 2 len(floor(m/2)).
"""
import random
import numpy as np

def mat3(n, blocks):
    M = np.zeros((3 * n, 3 * n), dtype=np.uint8)
    for (i, j), a in blocks.items():
        M[i*n:(i+1)*n, j*n:(j+1)*n] = a
    return M

def mul(A, B):
    return (A.astype(np.int64) @ B.astype(np.int64) % 2).astype(np.uint8)

def inv_unipotent(A, n):
    # A = 1 + N with N^2 = 0 in all uses below, so A^(-1) = 1 - N = 1 + N over F_2.
    I = np.eye(3 * n, dtype=np.uint8)
    N = (A ^ I)
    assert not mul(N, N).any()
    return A.copy()

def comm(A, B, n):
    return mul(mul(mul(A, B), inv_unipotent(A, n)), inv_unipotent(B, n))

def elem(n, a, i, j):
    I = np.eye(3 * n, dtype=np.uint8)
    return I ^ mat3(n, {(i, j): a})

def tree(n, leaves, i, k):
    """Return (group element, word length) equal to 1 + (prod leaves) E_ik."""
    if len(leaves) == 1:
        return elem(n, leaves[0], i, k), 1
    j = 3 - i - k  # the third index in {0,1,2}
    h = (len(leaves) + 1) // 2
    L, lL = tree(n, leaves[:h], i, j)
    R, lR = tree(n, leaves[h:], j, k)
    return comm(L, R, n), 2 * lL + 2 * lR

def rand_idem(n):
    # random idempotent P D P^(-1) over F_2
    while True:
        P = np.random.randint(0, 2, (n, n)).astype(np.uint8)
        if round(abs(np.linalg.det(P.astype(float)))) % 2 == 1:
            break
    D = np.diag(np.random.randint(0, 2, n)).astype(np.uint8)
    # inverse of P over F_2 by Gauss elimination
    A = np.concatenate([P.copy(), np.eye(n, dtype=np.uint8)], axis=1)
    r = 0
    for c in range(n):
        p = next(q for q in range(r, n) if A[q, c])
        A[[r, p]] = A[[p, r]]
        for q in range(n):
            if q != r and A[q, c]:
                A[q] ^= A[r]
        r += 1
    Pi = A[:, n:]
    E = mul(mul(P, D), Pi)
    assert (mul(E, E) == E).all()
    return E

def main():
    random.seed(1); np.random.seed(1)
    n = 5
    for m in [1, 2, 3, 4, 5, 7, 8, 13, 16]:
        for trial in range(20):
            leaves = [rand_idem(n) if trial % 2 else np.random.randint(0, 2, (n, n)).astype(np.uint8)
                      for _ in range(m)]
            g, ln = tree(n, leaves, 0, 2)
            prod = leaves[0]
            for a in leaves[1:]:
                prod = mul(prod, a)
            assert (g == elem(n, prod, 0, 2)).all(), (m, trial)
        print(f"m={m:2d}: identity holds on 20 trials, word length {ln} (<= 4 m^2 = {4*m*m})")
        assert ln <= 4 * m * m
    print("OK")

if __name__ == "__main__":
    main()
