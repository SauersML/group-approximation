"""Second eigenvalue of the L_j-orbit graphs of the Sym(d) family.

On the Cayley level of Sym(d) = <alpha = (0 1), beta = (0 1 ... d-1)>, every
L_j-orbit (j <= d-2) is a coset of H_j = Sym(S_j), |S_j| = m = d - j, and its
L_j-Schreier graph is the Cayley graph of Sym(m) for a transposition of two
cyclically adjacent points and an m-cycle.  This prints
  lambda_2 = second largest eigenvalue of (A + A^-1 + T + T^-1)/4
for m = 3..mmax, i.e. the 'old' eigenvalue that any lift of this level
inherits on the lifted L_j-orbits.
Usage: python3 spectral_sym.py mmax
"""
import sys
from itertools import permutations

import numpy as np
from scipy.sparse import lil_matrix
from scipy.sparse.linalg import eigsh


def main():
    mmax = int(sys.argv[1])
    for m in range(3, mmax + 1):
        els = list(permutations(range(m)))
        idx = {g: i for i, g in enumerate(els)}
        al = list(range(m)); al[0], al[1] = 1, 0
        cy = [(i + 1) % m for i in range(m)]
        N = len(els)
        M = lil_matrix((N, N))
        for g in els:
            i = idx[g]
            for s in (al, cy):
                h = tuple(s[g[k]] for k in range(m))
                M[i, idx[h]] += 0.25
                M[idx[h], i] += 0.25
        M = M.tocsr()
        if N <= 800:
            ev = np.sort(np.linalg.eigvalsh(M.toarray()))[::-1]
        else:
            ev = np.sort(eigsh(M, k=3, which='LA', return_eigenvectors=False))[::-1]
        print('m', m, '|Sym(m)|', N, 'lambda_2', round(float(ev[1]), 6), '1-lambda_2', round(1 - float(ev[1]), 6))
        sys.stdout.flush()


if __name__ == '__main__':
    main()
