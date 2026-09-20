"""Block direct sum of honest pairs: python3 dsum.py out.npz in1.npz in2.npz ...

An input may also be 'triv' (the trivial 1-dimensional representation) or 'rho2' (the
2-dimensional representation of 2I attaining (sqrt5-1)/2, read from the w20 census file
tbest_n2_a13_b12.npz).  The sum is an honest representation of Delta(4,3,5); it is used as a
reducible start point for fcensus.py seed mode (deformation off the reducible locus).
"""
import os
import sys
import numpy as np
from scipy.linalg import block_diag

HERE = os.path.dirname(os.path.abspath(__file__))
OLD = os.path.join(HERE, '..', 'thompson-t-triangle-rep-census-2026-09-17')


def load(name):
    if name == 'triv':
        return np.eye(1, dtype=complex), np.eye(1, dtype=complex)
    if name == 'rho2':
        name = os.path.join(OLD, 'tbest_n2_a13_b12.npz')
    f = np.load(name)
    return f['A'], f['B']


As, Bs = zip(*[load(x) for x in sys.argv[2:]])
A, B = block_diag(*As), block_diag(*Bs)
C5 = np.linalg.matrix_power(B @ A, 5)
print('n=%d  ||A^4-1||=%.1e ||B^3-1||=%.1e ||(BA)^5-1||=%.1e' % (
    A.shape[0], np.linalg.norm(np.linalg.matrix_power(A, 4) - np.eye(A.shape[0])),
    np.linalg.norm(np.linalg.matrix_power(B, 3) - np.eye(A.shape[0])), np.linalg.norm(C5 - np.eye(A.shape[0]))))
np.savez(sys.argv[1], A=A, B=B)
