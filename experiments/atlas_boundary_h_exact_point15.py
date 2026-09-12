"""Exact characteristic-zero certificate for the point15 atlas tangent screen.

The existing ``atlas_boundary_h_tangent_screen.py`` compares modular ranks.
Here we form the same integer Gram matrices, compute the boundary nullspace
over Q with SymPy, and verify exactly that every boundary-null vector is also
null for the four-generator H covariance Gram matrix.

This is deliberately only the 15-point permutation representation.  It closes
the characteristic-zero gap for that screen; it does not replace the regular
representation certificate needed for the nonlinear atlas collapse theorem.
"""

import json

import numpy as np
import sympy as sp

from atlas_boundary_h_tangent_screen import (
    INNER_ALIGNMENT_HEX,
    boundary_gram,
    h_gram,
)
from atlas_certified_a8_alignment import boundary_words
from atlas_two_chart_search import gf2_inv


def certificate():
    alignment = np.frombuffer(
        bytes.fromhex(INNER_ALIGNMENT_HEX), dtype=np.uint8
    ).reshape(4, 4).copy()
    alignment_inverse = gf2_inv(alignment)

    boundary = boundary_gram(
        boundary_words(), alignment, alignment_inverse, "point15")
    target = h_gram("point15")

    boundary_q = sp.Matrix(boundary.tolist())
    target_q = sp.Matrix(target.tolist())
    nullspace = boundary_q.nullspace()
    target_kills_boundary_kernel = all(
        target_q * vector == sp.zeros(target_q.rows, 1)
        for vector in nullspace
    )

    boundary_rank = boundary_q.rows - len(nullspace)
    target_rank = target_q.rank()
    kernels_equal = (
        target_kills_boundary_kernel and boundary_rank == target_rank
    )
    return {
        "model": "point15",
        "field": "Q",
        "boundary_relations": len(boundary_words()),
        "endomorphism_dimension": int(boundary_q.rows),
        "boundary_rank": int(boundary_rank),
        "boundary_nullity": int(len(nullspace)),
        "h_covariance_rank": int(target_rank),
        "h_covariance_nullity": int(target_q.rows - target_rank),
        "target_kills_boundary_kernel": bool(target_kills_boundary_kernel),
        "kernels_equal": bool(kernels_equal),
    }


def main():
    result = certificate()
    print(json.dumps(result, indent=2))
    if not result["kernels_equal"]:
        raise SystemExit("exact point15 tangent-kernel equality failed")


if __name__ == "__main__":
    main()
