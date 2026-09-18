#!/usr/bin/env python3
"""Mod-p Fox floor for the promotion cost Q_0 = relC(R_L; R_K).

L = F(a,b), K = <a, c>, c = b a b^-2.  A finite level is a transitive right
action of L on V = {0..n-1} given by permutations A, B (v.a = A[v]).

For each level we compute
  * B_direct = (t - 1) + codim_p, where t = number of K-orbits and
    codim_p = dim H_1(Y_L;F_p) - dim T(H_1(Y_K;F_p)), T = c-edge -> path b a b^-1 b^-1.
    Any level graphing Phi with K u Phi generating R_L needs >= B_direct edges.
  * k_u = dim ker (I - P_c - P_{cb}) on F_p^V   (Fox: d c / d b = 1 - c - cb).
Theorem 1 of the node says B_direct == k_u; the script checks it on small levels.
"""
import sys, random
import numpy as np

def rank_mod_p(M, p):
    M = np.array(M, dtype=np.int64) % p
    r, (rows, cols) = 0, M.shape
    for col in range(cols):
        if r == rows:
            break
        piv = np.nonzero(M[r:, col])[0]
        if piv.size == 0:
            continue
        i = r + piv[0]
        if i != r:
            M[[r, i]] = M[[i, r]]
        inv = pow(int(M[r, col]), p - 2, p)
        M[r] = (M[r] * inv) % p
        nz = np.nonzero(M[:, col])[0]
        nz = nz[nz != r]
        if nz.size:
            M[nz] = (M[nz] - np.outer(M[nz, col], M[r])) % p
        r += 1
    return r

def inv_perm(P):
    Q = [0] * len(P)
    for i, x in enumerate(P):
        Q[x] = i
    return Q

def word_perm(word, gens, n):
    """right action: v.(w1 w2 ...) = (...(v.w1).w2...)."""
    out = list(range(n))
    for ch in word:
        g = gens[ch]
        out = [g[v] for v in out]
    return out

def orbits(perms, n):
    seen, t = [False] * n, 0
    for s in range(n):
        if seen[s]:
            continue
        t += 1
        stack = [s]; seen[s] = True
        while stack:
            v = stack.pop()
            for P in perms:
                for w in (P[v],):
                    if not seen[w]:
                        seen[w] = True; stack.append(w)
            for P in perms:
                pass
        # inverse moves are covered because orbits of a permutation group are closed
    return t

def gens_of(A, B):
    n = len(A)
    return {'a': A, 'b': B, 'A': inv_perm(A), 'B': inv_perm(B)}, n

def k_u(A, B, p):
    g, n = gens_of(A, B)
    Pc = word_perm('baBB', g, n)
    Pcb = word_perm('baBBb', g, n)
    M = np.eye(n, dtype=np.int64)
    for v in range(n):
        M[v, Pc[v]] -= 1
        M[v, Pcb[v]] -= 1
    return n - rank_mod_p(M, p)

def b_direct(A, B, p):
    g, n = gens_of(A, B)
    Pc = word_perm('baBB', g, n)
    t = orbits([A, Pc], n)
    # chains of Y_L: index e_a(v) = v, e_b(v) = n + v
    def bd(edges):  # boundary matrix n x len(edges), edge = (src,dst)
        D = np.zeros((n, len(edges)), dtype=np.int64)
        for j, (s, d) in enumerate(edges):
            D[d, j] += 1; D[s, j] -= 1
        return D
    # T : C_1(Y_K) -> C_1(Y_L), K-edges: a-edge at v, c-edge at v
    T = np.zeros((2 * n, 2 * n), dtype=np.int64)
    Binv = g['B']
    for v in range(n):
        T[v, v] = 1                       # a-edge -> a-edge
        v1 = B[v]; T[n + v, n + v] += 1   # b-edge at v
        v2 = A[v1]; T[v1, n + v] += 1     # a-edge at v.b
        v3 = Binv[v2]; T[n + v3, n + v] -= 1  # backwards b-edge v3 -> v2
        v4 = Binv[v3]; T[n + v4, n + v] -= 1  # backwards b-edge v4 -> v3
        assert v4 == Pc[v]
    DK = bd([(v, A[v]) for v in range(n)] + [(v, Pc[v]) for v in range(n)])
    # H_1(Y_K) = ker DK ; image under T = T(ker DK).  dim T(ker DK) =
    # rank of [DK ; T] stacked minus rank DK  (rank of T restricted to ker DK)
    rT_on_Z = rank_mod_p(np.vstack([DK, T]), p) - rank_mod_p(DK, p)
    h1L = 2 * n - (n - 1)                 # Y_L connected
    return t - 1 + (h1L - rT_on_Z), t

def random_level(n, rng):
    A = list(range(n)); B = list(range(n))
    rng.shuffle(A); rng.shuffle(B)
    return A, B

def transitive(A, B):
    return orbits([A, B], len(A)) == 1

if __name__ == '__main__':
    rng = random.Random(20260917)
    print('# check B_direct == k_u on random transitive levels')
    bad = checked = nonzero = 0
    for trial in range(200):
        n = rng.randint(3, 40)
        A, B = random_level(n, rng)
        if not transitive(A, B):
            continue
        for p in (2, 3, 5, 7, 1000003):
            bd, t = b_direct(A, B, p)
            ku = k_u(A, B, p)
            checked += 1
            nonzero += (ku > 0)
            if bd != ku:
                bad += 1
                print('MISMATCH', n, p, bd, ku, t)
    print('checked (level, prime) pairs:', checked, ' with k_u > 0:', nonzero)
    print('mismatches:', bad)
    # small hand-made levels with many K-orbits: cyclic levels a -> +1, b -> 0
    for n in (4, 6, 9, 12):
        A = [(v + 1) % n for v in range(n)]; B = [(v + 2) % n for v in range(n)]
        for p in (2, 3, 5):
            bd, t = b_direct(A, B, p); ku = k_u(A, B, p)
            print(f'cyclic n={n} a=+1 b=+2 p={p}: t={t} B_direct={bd} k_u={ku}')
