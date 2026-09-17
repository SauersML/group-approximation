"""Structured initial points: exact BS packet (M,T) on Z/p and discrete-log matcher."""
import numpy as np

def primroot2(p):
    # is 2 a primitive root mod p?
    x, seen = 1, set()
    for _ in range(p - 1):
        x = (2 * x) % p
        seen.add(x)
    return len(seen) == p - 1

def perm_matrix(f, n):
    P = np.zeros((n, n), dtype=complex)
    for x in range(n):
        P[f[x], x] = 1.0
    return P

def packet(p):
    M = perm_matrix([(2 * x) % p for x in range(p)], p)
    T = perm_matrix([(x + 1) % p for x in range(p)], p)
    return M, T

def dlog_matcher(p):
    """K delta_{2^j} = delta_j (j=0..p-2), K delta_0 = delta_{p-1}; K M K^* ~ T."""
    assert primroot2(p)
    f = [0] * p
    x = 1
    for j in range(p - 1):
        f[x] = j
        x = (2 * x) % p
    f[0] = p - 1
    return perm_matrix(f, p)

def homogeneous_init(p, k=4):
    M, T = packet(p)
    K = dlog_matcher(p)
    g, X = [], M.copy()
    for i in range(k):
        g.append(X)
        X = K @ X @ K.conj().T
    return g, M, T, K
