"""Exact non-regularity certificates for permutation roots.

For a root tau in S_n of wbar over F <= S_n, Gamma = <F, tau> is finite, so the
Fox derivative D = sum_j eps_j s'_j is regular (no left annihilator in Z[Gamma])
iff it is a unit of Q[Gamma], iff rho(D) is invertible for every representation
rho of Gamma.  Here rho = natural permutation representation on n points
(and, if needed, on ordered pairs).  A zero determinant is an exact certificate
that the root is not regular; a non-zero one is inconclusive.
Composition convention as regroots.py: mul(a, b)[i] = a[b[i]].
"""
import itertools, sys, time
from fractions import Fraction
from regroots import mul, inv, ident, evalword

def fox_terms(word, tb, n):
    """List of (eps, s') with s' = prefix (t) or prefix*tau^-1 (t^-1)."""
    out = []; u = ident(n); ti = inv(tb)
    for kind, v in word:
        if kind == 'g':
            u = mul(u, v)
        elif v == 1:
            out.append((1, u)); u = mul(u, tb)
        else:
            u = mul(u, ti); out.append((-1, u))
    return out

def det_int(M):
    """Bareiss fraction-free determinant of an integer matrix (list of lists)."""
    A = [row[:] for row in M]; N = len(A); sign = 1; prev = 1
    for k in range(N - 1):
        if A[k][k] == 0:
            sw = next((i for i in range(k + 1, N) if A[i][k] != 0), None)
            if sw is None:
                return 0
            A[k], A[sw] = A[sw], A[k]; sign = -sign
        for i in range(k + 1, N):
            for j in range(k + 1, N):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    return sign * A[N - 1][N - 1]

def rep_matrix(terms, n, points):
    idx = {p: i for i, p in enumerate(points)}
    N = len(points); M = [[0] * N for _ in range(N)]
    for eps, g in terms:
        for p in points:
            q = tuple(g[x] for x in p)
            M[idx[q]][idx[p]] += eps
    return M

def certify(word, n, pairs=False):
    pts1 = [(i,) for i in range(n)]
    pts2 = [(i, j) for i in range(n) for j in range(n) if i != j]
    roots = 0; cert = 0; open_ = []
    for tb in itertools.permutations(range(n)):
        if evalword(word, tb, n) != ident(n):
            continue
        roots += 1
        terms = fox_terms(word, tb, n)
        if det_int(rep_matrix(terms, n, pts1)) == 0:
            cert += 1; continue
        if pairs and det_int(rep_matrix(terms, n, pts2)) == 0:
            cert += 1; continue
        open_.append(tb)
    return roots, cert, open_
