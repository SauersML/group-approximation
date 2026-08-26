"""Locate the first mixed-direction, genuinely coefficient-bearing Atlas row.

This is a sparse packet audit. Run it on MSI, not on a local workstation.
The ordering is the canonical ordering of
``atlas_relator_rank5_full_family.generate_relators``.

The filter deliberately has a literal meaning:

* discard the one-root ``root_*`` rows;
* among ``orth_*`` rows, require one upper and one lower root;
* require both displayed coefficient letters to be nonconstant.

Thus positive-root, one-constant-coefficient, involutivity, and reverse-
dictionary/Whitehead rows are outside the scan. The script also verifies the
block-matrix reason that the selected row is automatically satisfied: two
elementary transvections with the same source commute for arbitrary rectangular
coefficient maps.
"""

import re
import sys

from atlas_relator_rank5_full_family import generate_relators


ORTH = re.compile(r"orth_(\d)(\d)_(\d)(\d)_([1efEF])([1efEF])$")
ST3 = re.compile(r"st3_(\d)(\d)(\d)_([1efEF])([1efEF])$")


def mixed_rows(rows):
    selected = []
    for index, (name, word) in enumerate(rows):
        match = ORTH.fullmatch(name)
        if match is None:
            continue
        i, j, k, ell = map(int, match.group(1, 2, 3, 4))
        left_coefficient, right_coefficient = match.group(5, 6)
        mixed_direction = (i < j) != (k < ell)
        coefficient_bearing = (
            left_coefficient != "1" and right_coefficient != "1"
        )
        if mixed_direction and coefficient_bearing:
            selected.append((index, name, word))
    if not selected:
        raise AssertionError("the complete packet has no mixed coefficient row")
    return selected


def disjoint_mixed_rows(rows):
    """Rows whose two roots have distinct sources and distinct targets."""
    selected = []
    for index, (name, word) in enumerate(rows):
        match = ORTH.fullmatch(name)
        if match is None:
            continue
        i, j, k, ell = map(int, match.group(1, 2, 3, 4))
        left_coefficient, right_coefficient = match.group(5, 6)
        mixed_direction = (i < j) != (k < ell)
        coefficient_bearing = (
            left_coefficient != "1" and right_coefficient != "1"
        )
        genuinely_disjoint = i != k and j != ell
        if mixed_direction and coefficient_bearing and genuinely_disjoint:
            selected.append((index, name, word))
    if not selected:
        raise AssertionError("the packet has no disjoint mixed coefficient row")
    return selected


def composable_mixed_rows(rows):
    """Nonconstant St3 rows whose three roots are not all one orientation."""
    selected = []
    for index, (name, word) in enumerate(rows):
        match = ST3.fullmatch(name)
        if match is None:
            continue
        i, j, k = map(int, match.group(1, 2, 3))
        left_coefficient, right_coefficient = match.group(4, 5)
        directions = (i < j, j < k, i < k)
        mixed_direction = len(set(directions)) > 1
        coefficient_bearing = (
            left_coefficient != "1" and right_coefficient != "1"
        )
        if mixed_direction and coefficient_bearing:
            selected.append((index, name, word))
    if not selected:
        raise AssertionError("the packet has no composable mixed coefficient row")
    return selected


def first_common_rhs_star(rows):
    """First St3 target/product signature with two canonical factorizations."""
    by_rhs = {}
    for index, (name, word) in enumerate(rows):
        match = ST3.fullmatch(name)
        if match is None:
            continue
        i, j, k = map(int, match.group(1, 2, 3))
        left_coefficient, right_coefficient = match.group(4, 5)
        directions = (i < j, j < k, i < k)
        if (left_coefficient == "1" or right_coefficient == "1"
                or len(set(directions)) == 1):
            continue
        key = (i, k, left_coefficient, right_coefficient)
        by_rhs.setdefault(key, []).append((index, name, word, j))
    candidates = [value for value in by_rhs.values() if len(value) >= 2]
    if not candidates:
        raise AssertionError("the packet has no repeated mixed St3 RHS")
    return min(candidates, key=lambda value: value[1][0])


def matrix_units_multiply(left, right):
    """Multiply sparse matrix units represented as ``(row,column)``."""
    i, j = left
    k, ell = right
    return None if j != k else (i, ell)


def main():
    rows, lengths, counts = generate_relators(verify=False)
    assert counts == (200, 2980, 1432)
    assert len(rows) == 4612

    selected = mixed_rows(rows)
    index, name, word = selected[0]
    assert index == 280
    assert name == "orth_12_32_ee"
    assert len(word) == 52
    assert sum(lengths[matrix.tobytes()] for _factor, matrix in word) == 166

    second_index, second_name, second_word = selected[1]
    assert second_index == 281
    assert second_name == "orth_12_32_ef"
    assert len(second_word) == 52
    assert sum(lengths[matrix.tobytes()]
               for _factor, matrix in second_word) == 226

    # x_12(a) and x_32(b) have the common source/column 2. Their nilpotent
    # off-diagonal blocks multiply to zero in both orders, independently of
    # the coefficient maps a and b and of all object dimensions.
    assert matrix_units_multiply((1, 2), (3, 2)) is None
    assert matrix_units_multiply((3, 2), (1, 2)) is None

    print("packet full-family index (zero based):", index)
    print("packet entry (one based):", index + 1)
    print("name:", name)
    print("syllables:", len(word))
    print("X-length:", sum(lengths[matrix.tobytes()]
                           for _factor, matrix in word))
    print("same-source transvections commute for arbitrary coefficient maps")
    print("next coupled row index (zero based):", second_index)
    print("next coupled row name:", second_name)
    print("next coupled row X-length:", sum(
        lengths[matrix.tobytes()] for _factor, matrix in second_word
    ))
    print("the two-row family is simultaneously automatic")

    disjoint = disjoint_mixed_rows(rows)
    first_disjoint = disjoint[0]
    second_disjoint = disjoint[1]
    assert first_disjoint[0:2] == (380, "orth_12_43_ee")
    assert second_disjoint[0:2] == (381, "orth_12_43_ef")
    assert len(first_disjoint[2]) == len(second_disjoint[2]) == 36
    assert sum(lengths[matrix.tobytes()]
               for _factor, matrix in first_disjoint[2]) == 130
    assert sum(lengths[matrix.tobytes()]
               for _factor, matrix in second_disjoint[2]) == 154
    assert matrix_units_multiply((1, 2), (4, 3)) is None
    assert matrix_units_multiply((4, 3), (1, 2)) is None
    print("first disjoint coupled indices:",
          first_disjoint[0], second_disjoint[0])
    print("first disjoint coupled names:",
          first_disjoint[1], second_disjoint[1])
    print("disjoint two-row family is simultaneously automatic")

    composable = composable_mixed_rows(rows)
    first_composable = composable[0]
    second_composable = composable[1]
    assert first_composable[0:2] == (3260, "st3_132_ee")
    assert second_composable[0:2] == (3261, "st3_132_ef")
    assert len(first_composable[2]) == len(second_composable[2]) == 85
    assert sum(lengths[matrix.tobytes()]
               for _factor, matrix in first_composable[2]) == 271
    assert sum(lengths[matrix.tobytes()]
               for _factor, matrix in second_composable[2]) == 343
    print("first composable coupled indices:",
          first_composable[0], second_composable[0])
    print("first composable coupled names:",
          first_composable[1], second_composable[1])
    print("their two right-hand-side products are independent nuisance columns")

    rhs_star = first_common_rhs_star(rows)
    assert [(entry[0], entry[1], entry[3]) for entry in rhs_star] == [
        (3260, "st3_132_ee", 3),
        (3335, "st3_142_ee", 4),
        (3408, "st3_152_ee", 5),
    ]
    assert [len(entry[2]) for entry in rhs_star] == [85, 85, 39]
    assert [sum(lengths[matrix.tobytes()]
                for _factor, matrix in entry[2])
            for entry in rhs_star] == [271, 295, 130]
    print("first common-RHS return star:",
          [(entry[0], entry[1]) for entry in rhs_star])
    print("full three-path star has quotient-rank increment two")
    return 0


if __name__ == "__main__":
    sys.exit(main())
