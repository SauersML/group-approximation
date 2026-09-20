"""Exact commutants in L_{F_2}(1,2) restricted to the finite box V_{N,L}
(depth N, output words of length <= L), and a growth test for algebraic
independence of commuting pairs."""
import random, itertools, sys
from l2 import El, words, ONE, ZERO

def box_basis(N, L):
    outs = [w for l in range(L + 1) for w in words(l)]
    basis = []
    for m in words(N):
        for w in outs:
            T = {mm: frozenset() for mm in words(N)}
            T[m] = frozenset({w})
            basis.append(El(N, T))
    return basis

def flatten(e, D, index):
    e = e.extend(D)
    v = 0
    for m, S in e.T.items():
        for w in S:
            key = (m, w)
            if key not in index:
                index[key] = len(index)
            v ^= 1 << index[key]
    return v

def nullspace(vectors):
    """vectors: list of int bitsets (images of basis elements). Return basis of
    the kernel as bitsets over basis indices."""
    n = len(vectors)
    rows = []  # (pivot_bit, vec, combo)
    kernel = []
    pivots = {}
    for i, v in enumerate(vectors):
        c = 1 << i
        while v:
            p = v.bit_length() - 1
            if p in pivots:
                pv, pc = pivots[p]
                v ^= pv; c ^= pc
            else:
                pivots[p] = (v, c)
                break
        if not v:
            kernel.append(c)
    return kernel

def combo(basis, c):
    e = ZERO
    i = 0
    while c:
        if c & 1:
            e = e + basis[i]
        c >>= 1; i += 1
    return e

def commutant(A, N, L):
    basis = box_basis(N, L)
    D = A.N + N
    index = {}
    vecs = [flatten(A * b + b * A, D, index) for b in basis]
    ker = nullspace(vecs)
    return [combo(basis, c) for c in ker]

def rank(vecs):
    piv = {}
    r = 0
    for v in vecs:
        while v:
            p = v.bit_length() - 1
            if p in piv:
                v ^= piv[p]
            else:
                piv[p] = v; r += 1; break
    return r

def vec_of(sets, index):
    v = 0
    for S in sets:
        for w in S:
            if w not in index:
                index[w] = len(index)
            v ^= 1 << index[w]
    return v

def growth(A, B, k, zs):
    """rank of {A^i B^j : i+j<k} (k(k+1)/2 monomials) evaluated on delta_z for z in zs (lower bound
    for dim of span)."""
    index = {}
    # B^j delta_z
    cols = []
    for z in zs:
        cur = {z}
        Bj = []
        for j in range(k):
            Bj.append(cur)
            cur = B.act(cur)
        cols.append(Bj)
    vecs = []
    for j in range(k):
        cur = [cols[t][j] for t in range(len(zs))]
        for i in range(k - j):
            # tag each z-block separately
            vecs.append(vec_of([{('%d|' % t) + w for w in S} for t, S in enumerate(cur)], index))
            cur = [A.act(S) for S in cur]
    return rank(vecs)

def randz(n=300, seed=None):
    r = random.Random(seed)
    return ''.join(r.choice('01') for _ in range(n))
