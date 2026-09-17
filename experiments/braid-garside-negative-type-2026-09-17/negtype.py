"""Test whether a length function ell on B_n is conditionally negative definite on a finite set F:
K_ij = ell(g_i^{-1} g_j); ell is cnd on F iff P K P <= 0 where P projects onto sum-zero vectors."""
import sys, random
import numpy as np
from fractions import Fraction
from garside import Garside

def ball(G, r):
    gens = G.simples()
    seen = {(0, ()): 0}
    frontier = [(0, ())]
    for d in range(1, r + 1):
        nf = []
        for g in frontier:
            for s in gens:
                h = G.times(g, s)
                if h not in seen:
                    seen[h] = d
                    nf.append(h)
        frontier = nf
    return list(seen.keys())

def kernel(G, F, length=None):
    length = length or G.length
    N = len(F)
    inv = [G.inverse(g) for g in F]
    K = np.zeros((N, N))
    for i in range(N):
        for j in range(i, N):
            v = length(G.times(inv[i], F[j]))
            K[i, j] = K[j, i] = v
    return K

def top_eig(K):
    N = K.shape[0]
    P = np.eye(N) - np.ones((N, N)) / N
    M = P @ K @ P
    w, V = np.linalg.eigh(M)
    return w[-1], P @ V[:, -1]

def exact_witness(K, v, scale=1000):
    c = np.round(v / np.max(np.abs(v)) * scale).astype(int)
    c[np.argmax(np.abs(c))] -= c.sum()
    Ki = K.astype(int)
    val = int(c @ Ki @ c)
    return c, val

if __name__ == "__main__":
    n = int(sys.argv[1]); r = int(sys.argv[2])
    G = Garside(n)
    F = ball(G, r)
    print("n", n, "radius", r, "size", len(F))
    K = kernel(G, F)
    lam, v = top_eig(K)
    print("top eigenvalue of PKP:", lam)
    if lam > 1e-7:
        c, val = exact_witness(K, v)
        print("integer witness sum", c.sum(), "c^T K c =", val, "support", int((c != 0).sum()))
