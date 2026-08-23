#!/usr/bin/env python3
"""Audit the two designated cross-context raw-radical comparisons.

The S3-equivariant predicate compiler has generator space

    V = F_2^2 tensor V_inner

and commutator pencil ``H tensor S_f(x)``.  Write ``r_(a,0)`` and
``r_(a,1)`` for the two hot kernel words in the two outer coordinates, and
write ``ell_1, ell_2, ell_3=ell_1+ell_2`` for the radical-chart twists.

The upper and lower GL_2(F_2) transvections give the two comparisons needed
by the rank-one no-signalling chain:

    chart ell_1 --(fix r_(a,0))--> chart ell_3,
    chart ell_3 --(fix r_(a,1))--> chart ell_2.

This program checks those identities over F_2 for every marked atom and
every selector sector of the fixed Fanizza predicate menu.  It also chooses
the three reset hyperplanes equivariantly from one chart-ell_3 witness and
checks the full outside-word orbit data: projected-vector equality, linear
relations, symplectic Gram matrices, joint Pauli spectral multiplicities,
and the prescribed central-twist exponent.  Satisfying sectors are included;
they are not inferred from the forbidden-sector calculation.
"""

from __future__ import annotations

import json
from itertools import product
from typing import Callable

from radical_chart_common_hyperplane import (
    extended_form,
    hyperplane_basis,
    nullspace_vector,
    restricted_form,
    solve_f2,
)
from s3_equivariant_radical_compiler import (
    hyperbolic_tensor,
    symmetric_border,
)
from schur_clifford_rank_gate import BitTuple, eval_matrix, rank_f2


Predicate = tuple[int, Callable[[BitTuple], bool]]

FANIZZA_MENU: dict[str, Predicate] = {
    "C13/C14": (3, lambda value: value[2] == 1 and value[0] != value[1]),
    "C17": (3, lambda value: value[0] != (value[1] & value[2])),
    "C18 child-guard": (3, lambda value: value == (1, 0, 1)),
    "C18 four-bit residual": (4, lambda value: value == (1, 1, 1, 1)),
}


def dot(left: list[int], right: list[int]) -> int:
    return sum(a * b for a, b in zip(left, right)) & 1


def add(left: list[int], right: list[int]) -> list[int]:
    return [a ^ b for a, b in zip(left, right)]


def apply_form(matrix: list[list[int]], vector: list[int]) -> list[int]:
    return [dot(row, vector) for row in matrix]


def pairing(matrix: list[list[int]], left: list[int], right: list[int]) -> int:
    return dot(left, apply_form(matrix, right))


def transpose_action(
    transform: Callable[[list[int]], list[int]], functional: list[int]
) -> list[int]:
    """Return T^T functional by evaluating it on the standard basis."""
    size = len(functional)
    result = []
    for index in range(size):
        basis = [0] * size
        basis[index] = 1
        result.append(dot(functional, transform(basis)))
    return result


def outer_transvection(
    vector: list[int], inner_size: int, fixed_coordinate: int
) -> list[int]:
    """Apply the GL2 transvection fixing outer coordinate 0 or 1."""
    assert len(vector) == 2 * inner_size + 1
    first = vector[:inner_size]
    second = vector[inner_size : 2 * inner_size]
    tail = vector[-1:]
    if fixed_coordinate == 0:
        # [[1,1],[0,1]]: fixes the first outer coordinate.
        return add(first, second) + second + tail
    if fixed_coordinate == 1:
        # [[1,0],[1,1]]: fixes the second outer coordinate.
        return first + add(first, second) + tail
    raise ValueError(fixed_coordinate)


def congruent(
    source: list[list[int]],
    target: list[list[int]],
    transform: Callable[[list[int]], list[int]],
) -> bool:
    """Check source = T^T target T on every pair of basis vectors."""
    size = len(source)
    images = []
    for index in range(size):
        basis = [0] * size
        basis[index] = 1
        images.append(transform(basis))
    return all(
        source[row][column]
        == pairing(target, images[row], images[column])
        for row in range(size)
        for column in range(size)
    )


def raw_words(
    forbidden: list[BitTuple],
    supports: dict[BitTuple, tuple[int, int]],
    inner_size: int,
) -> list[tuple[list[int], list[int]]]:
    words = []
    for assignment in forbidden:
        start, stop = supports[assignment]
        kernel = [0] * inner_size
        for index in range(start, stop):
            kernel[index] = 1
        words.append(
            (
                kernel + [0] * inner_size + [0],
                [0] * inner_size + kernel + [0],
            )
        )
    return words


def vector_rank(vectors: list[list[int]]) -> int:
    if not vectors:
        return 0
    return rank_f2([vector[:] for vector in vectors])


def relation_masks(vectors: list[list[int]]) -> tuple[int, ...]:
    relations = []
    for mask in range(1 << len(vectors)):
        total = [0] * len(vectors[0])
        for index, vector in enumerate(vectors):
            if (mask >> index) & 1:
                total = add(total, vector)
        if not any(total):
            relations.append(mask)
    return tuple(relations)


def gram(matrix: list[list[int]], vectors: list[list[int]]) -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(pairing(matrix, left, right) for right in vectors)
        for left in vectors
    )


def projected_words(
    words: list[tuple[list[int], list[int]]],
    coordinate: int,
    radical: list[int],
    hyperplane_functional: list[int],
) -> tuple[list[list[int]], tuple[int, ...]]:
    vectors = []
    radical_coefficients = []
    for pair in words:
        word = pair[coordinate]
        coefficient = dot(hyperplane_functional, word)
        projected = add(word, radical) if coefficient else word[:]
        assert dot(hyperplane_functional, projected) == 0
        vectors.append(projected)
        radical_coefficients.append(coefficient)
    return vectors, tuple(radical_coefficients)


def audit_predicate(name: str, predicate: Predicate) -> dict:
    arity, forbidden_test = predicate
    assignments = list(product((0, 1), repeat=arity))
    forbidden = [assignment for assignment in assignments if forbidden_test(assignment)]
    symmetric, supports, _ = symmetric_border(arity, forbidden)
    alternating_affine = hyperbolic_tensor(symmetric, arity)
    inner_size = len(symmetric)
    vector_size = len(alternating_affine)
    words = raw_words(forbidden, supports, inner_size)

    ell_1 = [0] * vector_size
    ell_2 = [0] * vector_size
    for start, _ in supports.values():
        ell_1[start] = 1
        ell_2[inner_size + start] = 1
    ell_3 = add(ell_1, ell_2)
    functionals = [ell_1, ell_2, ell_3]

    forms: list[list[list[list[int]]]] = []
    radicals: list[list[list[int]]] = []
    for functional in functionals:
        chart_forms = [
            extended_form(eval_matrix(alternating_affine, assignment), functional)
            for assignment in assignments
        ]
        forms.append(chart_forms)
        radicals.append([nullspace_vector(matrix) for matrix in chart_forms])

    # Choose beta=ell_3 first.  Transport its hyperplane by the two S3
    # transvections, so the outside-word comparison is built into the reset
    # subgroup identifications rather than imposed after independent choices.
    phi_beta = solve_f2(radicals[2], [1] * len(assignments))
    assert phi_beta is not None
    fix_r0 = lambda vector: outer_transvection(vector, inner_size, 0)
    fix_r1 = lambda vector: outer_transvection(vector, inner_size, 1)
    phi_alpha = transpose_action(fix_r0, phi_beta)
    phi_gamma = transpose_action(fix_r1, phi_beta)
    phis = [phi_alpha, phi_gamma, phi_beta]

    for chart in range(3):
        assert all(dot(phis[chart], radical) == 1 for radical in radicals[chart])
        basis = hyperplane_basis(phis[chart])
        assert all(
            rank_f2(restricted_form(matrix, basis)) == vector_size
            for matrix in forms[chart]
        )

    comparisons = (
        {
            "coordinate": 0,
            "source_chart": 0,
            "target_chart": 2,
            "transform": fix_r0,
            "label": "ell_1->ell_3 fixes r_(a,0)",
        },
        {
            "coordinate": 1,
            "source_chart": 2,
            "target_chart": 1,
            "transform": fix_r1,
            "label": "ell_3->ell_2 fixes r_(a,1)",
        },
    )

    comparison_reports = []
    for comparison in comparisons:
        coordinate = comparison["coordinate"]
        source = comparison["source_chart"]
        target = comparison["target_chart"]
        transform = comparison["transform"]
        sector_reports = []
        for assignment_index, assignment in enumerate(assignments):
            source_form = forms[source][assignment_index]
            target_form = forms[target][assignment_index]
            source_radical = radicals[source][assignment_index]
            target_radical = radicals[target][assignment_index]

            assert congruent(source_form, target_form, transform)
            assert transform(source_radical) == target_radical
            assert all(transform(pair[coordinate]) == pair[coordinate] for pair in words)

            source_vectors, source_coefficients = projected_words(
                words,
                coordinate,
                source_radical,
                phis[source],
            )
            target_vectors, target_coefficients = projected_words(
                words,
                coordinate,
                target_radical,
                phis[target],
            )
            assert [transform(vector) for vector in source_vectors] == target_vectors
            assert relation_masks(source_vectors) == relation_masks(target_vectors)
            assert gram(source_form, source_vectors) == gram(target_form, target_vectors)

            tuple_rank = vector_rank(source_vectors)
            assert tuple_rank == len(forbidden)
            assert not any(any(row) for row in gram(source_form, source_vectors))

            # Both ell functionals take value one on their shared raw word,
            # so (ell_source-ell_target)(r)=0 in F_2.  The lifted
            # transvection fixes every generator in the relevant outer half;
            # therefore its phase-root correction on the raw product is also
            # exactly zero, not merely spectrally invisible.
            twist_exponents = tuple(
                dot(add(functionals[source], functionals[target]), pair[coordinate])
                for pair in words
            )
            assert twist_exponents == (0,) * len(words)

            spin_dimension = 1 << (vector_size // 2)
            joint_spectral_multiplicity = spin_dimension >> tuple_rank
            assert joint_spectral_multiplicity > 0
            sector_reports.append(
                {
                    "assignment": "".join(map(str, assignment)),
                    "forbidden": assignment in forbidden,
                    "tuple_rank": tuple_rank,
                    "isotropic": True,
                    "joint_spectral_multiplicity": joint_spectral_multiplicity,
                    "source_radical_coefficients": list(source_coefficients),
                    "target_radical_coefficients": list(target_coefficients),
                    "central_twist_exponents": list(twist_exponents),
                }
            )

        comparison_reports.append(
            {
                "label": comparison["label"],
                "sectors_checked": len(sector_reports),
                "satisfying_sectors_checked": sum(
                    not sector["forbidden"] for sector in sector_reports
                ),
                "forbidden_sectors_checked": sum(
                    sector["forbidden"] for sector in sector_reports
                ),
                "all_raw_words_fixed_exactly": True,
                "all_phase_root_corrections_zero": True,
                "all_joint_spectra_match": True,
                "sectors": sector_reports,
            }
        )

    return {
        "predicate": name,
        "arity": arity,
        "marked_atoms": len(forbidden),
        "selector_sectors": len(assignments),
        "chart_spin_dimension": 1 << (vector_size // 2),
        "comparisons": comparison_reports,
    }


def main() -> None:
    reports = [audit_predicate(name, predicate) for name, predicate in FANIZZA_MENU.items()]
    summary = {
        "predicates_checked": len(reports),
        "marked_atoms_checked": sum(report["marked_atoms"] for report in reports),
        "selector_blocks_checked": sum(
            comparison["sectors_checked"]
            for report in reports
            for comparison in report["comparisons"]
        ),
        "satisfying_blocks_checked": sum(
            comparison["satisfying_sectors_checked"]
            for report in reports
            for comparison in report["comparisons"]
        ),
        "forbidden_blocks_checked": sum(
            comparison["forbidden_sectors_checked"]
            for report in reports
            for comparison in report["comparisons"]
        ),
        "central_twists_checked": sum(
            report["marked_atoms"] * comparison["sectors_checked"]
            for report in reports
            for comparison in report["comparisons"]
        ),
        "result": "all designated outside-word tuples are exactly S3-conjugate",
        "reports": reports,
    }
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
