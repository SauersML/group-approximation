#!/usr/bin/env sage
"""Exact component centralizer and invariant-subspace audit in GL(4,4)."""

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sage.all import GF, Matrix, VectorSpace, libgap

from atlas_a4_19243_component_localization import H6_LABELS, H18_LABELS


def lifted(value, field):
    return Matrix(field, [[int(entry) for entry in row] for row in value])


def commutant(matrices, field):
    equations = []
    for matrix in matrices:
        for i in range(4):
            for j in range(4):
                row = [field.zero()] * 16
                for k in range(4):
                    row[4 * i + k] += matrix[k, j]
                    row[4 * k + j] -= matrix[i, k]
                equations.append(row)
    basis_vectors = Matrix(field, equations).right_kernel().basis()
    basis = [Matrix(field, 4, 4, vector) for vector in basis_vectors]
    coefficient_space = VectorSpace(field, len(basis))
    invertible = 0
    for coefficients in coefficient_space:
        value = sum((coefficient * matrix for coefficient, matrix
                     in zip(coefficients, basis)), Matrix.zero(field, 4, 4))
        if value.is_invertible():
            invertible += 1
    return len(basis), invertible


def main():
    field = GF(4, "z")
    result = {}
    all_matrices = []
    for name, labels in (("H6", H6_LABELS), ("H18", H18_LABELS)):
        matrices = [lifted(value, field) for value in labels]
        all_matrices.extend(matrices)
        subgroup = libgap.Group([matrix._libgap_() for matrix in matrices])
        dimension, units = commutant(matrices, field)
        result[name] = {
            "order": int(subgroup.Size()),
            "commutant_dimension_over_F4": dimension,
            "centralizer_order": units,
        }
    join = libgap.Group([matrix._libgap_() for matrix in all_matrices])
    common_dimension, common_units = commutant(all_matrices, field)
    result["join_order"] = int(join.Size())
    result["common_commutant_dimension_over_F4"] = common_dimension
    result["common_centralizer_order"] = common_units
    binary = GF(2)
    for name, labels in (("H6", H6_LABELS), ("H18", H18_LABELS)):
        matrices = [lifted(value, binary) for value in labels]
        dimension, units = commutant(matrices, binary)
        result[name]["commutant_dimension_over_F2"] = dimension
        result[name]["centralizer_order_over_F2"] = units
    binary_all = [lifted(value, binary) for value in H6_LABELS + H18_LABELS]
    binary_common_dimension, binary_common_units = commutant(binary_all, binary)
    result["common_commutant_dimension_over_F2"] = binary_common_dimension
    result["common_centralizer_order_over_F2"] = binary_common_units
    assert result == {
        "H6": {
            "order": 6,
            "commutant_dimension_over_F4": 5,
            "centralizer_order": 540,
            "commutant_dimension_over_F2": 5,
            "centralizer_order_over_F2": 6,
        },
        "H18": {
            "order": 18,
            "commutant_dimension_over_F4": 3,
            "centralizer_order": 27,
            "commutant_dimension_over_F2": 3,
            "centralizer_order_over_F2": 3,
        },
        "join_order": 20160,
        "common_commutant_dimension_over_F4": 1,
        "common_centralizer_order": 3,
        "common_commutant_dimension_over_F2": 1,
        "common_centralizer_order_over_F2": 1,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
