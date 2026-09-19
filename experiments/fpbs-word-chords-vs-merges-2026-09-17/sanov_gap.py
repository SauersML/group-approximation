"""Spectral gap of the Sanov 3-adic tower (evidence only; the proof cites
Selberg / property (tau), or Bourgain-Gamburd for p-power levels).

L = F(a, b) acts on SL_2(Z/3^k) by right multiplication, a -> [[1,2],[0,1]],
b -> [[1,0],[2,1]].  The action is transitive (the Sanov group surjects onto
SL_2(Z/3^k)) and the inverse limit SL_2(Z_3) is a free profinite action,
since the Sanov group is free and embeds in SL_2(Z_3).
lam2 = second largest eigenvalue of M = (a + a^-1 + b + b^-1)/4 (self-adjoint).
Theorem S then gives sigma_b >= (1 - sup_k lam2_k)/4.

Usage: python3 sanov_gap.py kmax
"""
import sys
import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as sla


def elements(N):
    out = []
    for a in range(N):
        for b in range(N):
            for c in range(N):
                for d in range(N):
                    if (a * d - b * c) % N == 1:
                        out.append((a, b, c, d))
    return out


def mul(x, y, N):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % N, (a * f + b * h) % N,
            (c * e + d * g) % N, (c * f + d * h) % N)


def inv(x, N):
    a, b, c, d = x
    return (d % N, (-b) % N, (-c) % N, a % N)


def run(kmax):
    for k in range(1, kmax + 1):
        N = 3 ** k
        els = elements(N)
        idx = {e: i for i, e in enumerate(els)}
        n = len(els)
        A = (1, 2, 0, 1)
        B = (1, 0, 2, 1)
        gens = [A, inv(A, N), B, inv(B, N)]
        rows, cols = [], []
        for i, e in enumerate(els):
            for g in gens:
                rows.append(i)
                cols.append(idx[mul(e, g, N)])
        M = sp.csr_matrix((np.full(len(rows), 0.25), (rows, cols)), shape=(n, n))
        # transitivity check
        seen = {0}
        st = [0]
        while st:
            u = st.pop()
            for v in M.indices[M.indptr[u]:M.indptr[u + 1]]:
                if v not in seen:
                    seen.add(v)
                    st.append(v)
        if n <= 800:
            ev = np.sort(np.linalg.eigvalsh(M.toarray()))[::-1]
        else:
            ev = np.sort(sla.eigsh(M, k=3, which='LA', return_eigenvectors=False))[::-1]
        lam2 = ev[1]
        print('k', k, 'n', n, 'transitive', len(seen) == n, 'lam1 %.6f' % ev[0],
              'lam2 %.6f' % lam2, '(1-lam2)/4 %.6f' % ((1 - lam2) / 4))
        sys.stdout.flush()


if __name__ == '__main__':
    run(int(sys.argv[1]))
