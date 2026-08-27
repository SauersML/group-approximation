"""Exact trivial-character projective charts for the SL(3,Z) presentation.

The nonzero-vector chart splits under scalar multiplication.  This module
constructs only its trivial scalar-character block, equivalently the exact
action on ``P^2(F_p)``.  Coefficients are integral and no floating roots of
unity are evaluated.
"""

import numpy as np
from scipy.sparse import coo_matrix

from sl3_character_block_spectrum import exact_block_pattern


def integral_sparse(entries, shape):
    rows, columns, signs, _exponents = entries
    result = coo_matrix(
        (signs.astype(np.int64), (rows, columns)), shape=shape,
        dtype=np.int64)
    result.sum_duplicates()
    return result.tocsr()


def projective_coboundaries(prime):
    pattern = exact_block_pattern(prime)
    d0 = integral_sparse(
        pattern["d0"], (pattern["edges"], pattern["vertices"]))
    d1 = integral_sparse(
        pattern["d1"], (pattern["cells"], pattern["edges"]))
    chain = d1 @ d0
    if chain.nnz and np.max(np.abs(chain.data)) != 0:
        raise AssertionError("projective d1 d0 is nonzero")
    return pattern["relator_names"], pattern["vertices"], d0, d1
