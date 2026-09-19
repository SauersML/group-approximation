#!/usr/bin/env python3
"""Third, matrix-only check of the head-keeping finite quotient of Gamma_trap.

N_W x| G0 embeds in GL_{2n+1}(F_2):
    (w, Z) -> U(w, Z) = [[I, w, Z], [0, 1, w^T], [0, 0, I]]   (blocks n, 1, n)
    A      -> D(A)    = diag(A, 1, A^{-T})
since U(w,Z) U(w',Z') = U(w+w', Z+Z'+w w'^T) and
D(A) U(w,Z) D(A)^{-1} = U(Aw, A Z A^T).  Every generator is a (2n+1)-square
F_2 matrix and every word is evaluated by plain matrix multiplication.

For the finite group G = image / U(0, K): a relator l = r holds in G iff
l^{-1} r = U(0, D) with D in K, where K is any G0-stable subspace of the
n x n matrices (U(0, K) is then central and normal).  We take K = the
G0-span of those D's, check that every relator has the form U(0, D), and that
h = U(0, H) with H not in K.  Nothing from tensor_model or verify_hit is used;
the Levi matrices come from tensor_search.ring_module (any commuting families
of involutions would give a valid group; the relators check this too).
Usage: python3 check_matrix.py [seed]   (c_u is random from the seed)
"""

import random
import sys

import numpy as np

from tensor_search import ring_module
from words import DERIVED, TRAP_RELS, INVOL_RELS, EXTRA_RELS, LEFT, RIGHT


def mm(A, B):
    return (A.astype(np.int64) @ B.astype(np.int64) % 2).astype(np.uint8)


def inv2(M):
    """Inverse over F_2 by Gauss-Jordan."""
    m = M.shape[0]
    A = np.concatenate([M.copy(), np.eye(m, dtype=np.uint8)], axis=1)
    r = 0
    for c in range(m):
        piv = next(i for i in range(r, m) if A[i, c])
        A[[r, piv]] = A[[piv, r]]
        for i in range(m):
            if i != r and A[i, c]:
                A[i] ^= A[r]
        r += 1
    return A[:, m:]


def U(w, Z, n):
    M = np.eye(2 * n + 1, dtype=np.uint8)
    M[:n, n] = w
    M[:n, n + 1:] = Z
    M[n, n + 1:] = w
    return M


def D(A, n):
    M = np.zeros((2 * n + 1, 2 * n + 1), np.uint8)
    M[:n, :n] = A
    M[n, n] = 1
    M[n + 1:, n + 1:] = inv2(A).T
    return M


def central_part(M, n):
    """Z if M = U(0, Z), else None."""
    E = M.copy()
    Z = E[:n, n + 1:].copy()
    E[:n, n + 1:] = 0
    return Z if not (E ^ np.eye(2 * n + 1, dtype=np.uint8)).any() else None


def span_closure(gens, mats, n):
    piv = {}

    def red(v):
        for p in sorted(piv, reverse=True):
            if v >> p & 1:
                v ^= piv[p]
        return v

    def asint(Z):
        return int("".join(str(int(b)) for b in Z.reshape(-1)[::-1]), 2)

    def asmat(v):
        return np.array([v >> b & 1 for b in range(n * n)], np.uint8).reshape(n, n)

    queue = [asint(Z) for Z in gens]
    while queue:
        v = red(queue.pop())
        if not v:
            continue
        piv[v.bit_length() - 1] = v
        for A in mats.values():
            queue.append(asint(mm(mm(A, asmat(v)), A.T)))
    return lambda Z: red(asint(Z)) == 0, len(piv)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    extra = len(sys.argv) > 2 and sys.argv[2] == "extra"
    mats, v = ring_module(0b10001)
    n = v.shape[0]
    rng = random.Random(seed)
    cu = np.array([[rng.randint(0, 1) for _ in range(n)] for _ in range(n)], np.uint8)
    val = {g: D(mats[g], n) for g in LEFT + RIGHT}
    val["u"] = U(v, cu, n)
    for name, wd in DERIVED:
        M = np.eye(2 * n + 1, dtype=np.uint8)
        for g in wd:
            M = mm(M, val[g])
        val[name] = M

    def ev(wd):
        M = np.eye(2 * n + 1, dtype=np.uint8)
        for g in wd:
            M = mm(M, val[g])
        return M

    rels = TRAP_RELS + INVOL_RELS + (EXTRA_RELS if extra else [])
    gens, bad = [], []
    for name, l, r in rels:
        Zd = central_part(mm(inv2(ev(l)), ev(r)), n)
        if Zd is None:
            bad.append(name)
        else:
            gens.append(Zd)
    inK, dimK = span_closure(gens, mats, n)
    H = central_part(val["h"], n)
    print("seed %d, %d relators (extra=%s): non-central relator quotients %s"
          % (seed, len(rels), extra, bad))
    print("dim K = %d of %d; h = U(0,H): %s; H in K: %s -> head %s in G"
          % (dimK, n * n, H is not None, inK(H), "dies" if inK(H) else "SURVIVES"))


if __name__ == "__main__":
    main()
