#!/usr/bin/env python3
"""Search tensor-fusion detectors in the order-128 support packet.

The packet has central basis (J,z_e,z_f) and evaluated commutation matrix
[[j,j+e],[f,0]].  This script constructs all 38 irreducible representations
explicitly in Pauli normal form, verifies their character orthogonality, and
computes the complete fusion table.  It then searches for an irreducible or
two-irrep tensor coefficient whose commutant expansion is concentrated on the
forbidden central character 101.

Only the Python standard library is used.  Matrices have size at most four.
"""
from __future__ import annotations

import json
import hashlib
from itertools import combinations_with_replacement, product


Bit2 = tuple[int, int]
Bit3 = tuple[int, int, int]
Matrix2F = tuple[Bit2, Bit2]
Matrix3F = tuple[Bit3, Bit3, Bit3]
ComplexMatrix = tuple[tuple[complex, ...], ...]

I2: ComplexMatrix = ((1, 0), (0, 1))
X: ComplexMatrix = ((0, 1), (1, 0))
Z: ComplexMatrix = ((1, 0), (0, -1))
GL2: tuple[Matrix2F, ...] = tuple(
    matrix
    for flat in product((0, 1), repeat=4)
    for matrix in [((flat[0], flat[1]), (flat[2], flat[3]))]
    if (matrix[0][0] * matrix[1][1] ^ matrix[0][1] * matrix[1][0]) == 1
)


def rank_f2(rows: list[list[int]]) -> int:
    work = [row[:] for row in rows]
    pivot_row = 0
    for column in range(len(work[0])):
        pivot = next((row for row in range(pivot_row, len(work)) if work[row][column]), None)
        if pivot is None:
            continue
        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        for row in range(len(work)):
            if row != pivot_row and work[row][column]:
                work[row] = [a ^ b for a, b in zip(work[row], work[pivot_row])]
        pivot_row += 1
    return pivot_row


GL3: tuple[Matrix3F, ...] = tuple(
    matrix
    for flat in product((0, 1), repeat=9)
    for matrix in [
        (tuple(flat[0:3]), tuple(flat[3:6]), tuple(flat[6:9]))
    ]
    if rank_f2([list(row) for row in matrix]) == 3
)  # type: ignore[assignment]
GROUP_ELEMENTS = tuple(product((0, 1), repeat=7))
FORBIDDEN: Bit3 = (1, 0, 1)
ALLOWED_J_MINUS: tuple[Bit3, ...] = ((1, 0, 0), (1, 1, 0), (1, 1, 1))


def identity(size: int) -> ComplexMatrix:
    return tuple(tuple(1 if i == j else 0 for j in range(size)) for i in range(size))


def matmul(left: ComplexMatrix, right: ComplexMatrix) -> ComplexMatrix:
    size = len(left)
    return tuple(
        tuple(sum(left[i][k] * right[k][j] for k in range(size)) for j in range(size))
        for i in range(size)
    )


def trace(matrix: ComplexMatrix) -> complex:
    return sum(matrix[i][i] for i in range(len(matrix)))


def kron(left: ComplexMatrix, right: ComplexMatrix) -> ComplexMatrix:
    return tuple(
        tuple(
            left[i // len(right)][j // len(right)]
            * right[i % len(right)][j % len(right)]
            for j in range(len(left) * len(right))
        )
        for i in range(len(left) * len(right))
    )


def f2_matmul(left: Matrix2F, right: Matrix2F) -> Matrix2F:
    return tuple(
        tuple(
            (left[i][0] & right[0][j]) ^ (left[i][1] & right[1][j])
            for j in range(2)
        )
        for i in range(2)
    )  # type: ignore[return-value]


def transpose(matrix: Matrix2F) -> Matrix2F:
    return ((matrix[0][0], matrix[1][0]), (matrix[0][1], matrix[1][1]))


def mat3_vec(matrix: Matrix3F, vector: Bit3) -> Bit3:
    return tuple(
        sum(matrix[i][j] & vector[j] for j in range(3)) & 1 for i in range(3)
    )  # type: ignore[return-value]


def transpose3(matrix: Matrix3F) -> Matrix3F:
    return tuple(tuple(matrix[i][j] for i in range(3)) for j in range(3))  # type: ignore[return-value]


def inverse2(matrix: Matrix2F) -> Matrix2F:
    # Every invertible 2-by-2 binary matrix has determinant one.
    return ((matrix[1][1], matrix[0][1]), (matrix[1][0], matrix[0][0]))


def rank2(matrix: Matrix2F) -> int:
    if matrix == ((0, 0), (0, 0)):
        return 0
    determinant = (matrix[0][0] & matrix[1][1]) ^ (matrix[0][1] & matrix[1][0])
    return 2 if determinant else 1


def commutation_matrix(character: Bit3) -> Matrix2F:
    j, e, f = character
    return ((j, j ^ e), (f, 0))


COMMUTATOR_WORDS: tuple[tuple[Bit3, Bit3], tuple[Bit3, Bit3]] = (
    ((1, 0, 0), (1, 1, 0)),
    ((0, 0, 1), (0, 0, 0)),
)


def add3(left: Bit3, right: Bit3) -> Bit3:
    return tuple(a ^ b for a, b in zip(left, right))  # type: ignore[return-value]


def transformed_word(row: Bit2, column: Bit2) -> Bit3:
    output: Bit3 = (0, 0, 0)
    for i in range(2):
        for j in range(2):
            if row[i] & column[j]:
                output = add3(output, COMMUTATOR_WORDS[i][j])
    return output


def packet_linear_automorphisms() -> list[tuple[Matrix2F, Matrix2F, Matrix3F]]:
    automorphisms = []
    for row_change, column_change, center_change in product(GL2, GL2, GL3):
        valid = True
        for i in range(2):
            for j in range(2):
                source_word = COMMUTATOR_WORDS[i][j]
                image_word = mat3_vec(center_change, source_word)
                target_word = transformed_word(row_change[i], column_change[j])
                if image_word != target_word:
                    valid = False
                    break
            if not valid:
                break
        if valid:
            automorphisms.append((row_change, column_change, center_change))
    return automorphisms


def diagonalize(matrix: Matrix2F) -> tuple[Matrix2F, Matrix2F, int]:
    rank = rank2(matrix)
    target: Matrix2F
    if rank == 0:
        target = ((0, 0), (0, 0))
    elif rank == 1:
        target = ((1, 0), (0, 0))
    else:
        target = ((1, 0), (0, 1))
    for left, right in product(GL2, repeat=2):
        if f2_matmul(f2_matmul(left, matrix), transpose(right)) == target:
            return left, right, rank
    raise AssertionError(matrix)


def pauli_on(qubits: int, index: int, matrix: ComplexMatrix) -> ComplexMatrix:
    output = ((1,),)
    for qubit in range(qubits):
        output = kron(output, matrix if qubit == index else I2)
    return output


def product_selected(generators: tuple[ComplexMatrix, ...], bits: Bit2) -> ComplexMatrix:
    output = identity(len(generators[0]))
    for generator, bit in zip(generators, bits):
        if bit:
            output = matmul(output, generator)
    return output


def clean(value: complex) -> complex:
    real = round(value.real)
    imag = round(value.imag)
    if abs(value.real - real) > 1e-8 or abs(value.imag - imag) > 1e-8:
        raise AssertionError(value)
    return complex(real, imag)


class Irrep:
    def __init__(self, character: Bit3, radical_signs: tuple[int, ...]):
        self.character = character
        left, right, self.rank = diagonalize(commutation_matrix(character))
        self.dimension = 1 << self.rank
        new_p = []
        new_q = []
        sign_index = 0
        for index in range(2):
            if index < self.rank:
                new_p.append(pauli_on(self.rank, index, Z))
                new_q.append(pauli_on(self.rank, index, X))
            else:
                p_sign = -1 if radical_signs[sign_index] else 1
                q_sign = -1 if radical_signs[sign_index + 1] else 1
                sign_index += 2
                new_p.append(tuple(tuple(p_sign * value for value in row) for row in identity(self.dimension)))
                new_q.append(tuple(tuple(q_sign * value for value in row) for row in identity(self.dimension)))
        left_inverse = inverse2(left)
        right_inverse = inverse2(right)
        self.p = tuple(product_selected(tuple(new_p), row) for row in left_inverse)
        self.q = tuple(product_selected(tuple(new_q), row) for row in right_inverse)
        self.label = "".join(map(str, character)) + ":" + "".join(map(str, radical_signs))
        self.values = tuple(self.character_value(element) for element in GROUP_ELEMENTS)

    def character_value(self, element: tuple[int, ...]) -> complex:
        p_bits: Bit2 = (element[0], element[1])
        q_bits: Bit2 = (element[2], element[3])
        center: Bit3 = (element[4], element[5], element[6])
        central_sign = -1 if sum(a & b for a, b in zip(self.character, center)) & 1 else 1
        matrix = matmul(product_selected(self.p, p_bits), product_selected(self.q, q_bits))
        return clean(central_sign * trace(matrix))


def irreps() -> list[Irrep]:
    output = []
    for character in product((0, 1), repeat=3):
        rank = rank2(commutation_matrix(character))
        for signs in product((0, 1), repeat=2 * (2 - rank)):
            output.append(Irrep(character, signs))
    assert len(output) == 38
    assert sum(irrep.dimension**2 for irrep in output) == 128
    return output


def inner(left: tuple[complex, ...], right: tuple[complex, ...]) -> int:
    value = sum(a * b.conjugate() for a, b in zip(left, right)) / 128
    cleaned = clean(value)
    if cleaned.imag or cleaned.real < 0:
        raise AssertionError(cleaned)
    return int(cleaned.real)


def tensor_values(left: tuple[complex, ...], right: tuple[complex, ...]) -> tuple[complex, ...]:
    return tuple(a * b for a, b in zip(left, right))


def fusion(left: Irrep, right_values: tuple[complex, ...], all_irreps: list[Irrep]) -> list[int]:
    values = tensor_values(left.values, right_values)
    multiplicities = [inner(values, target.values) for target in all_irreps]
    assert sum(m * target.dimension for m, target in zip(multiplicities, all_irreps)) == left.dimension * int(right_values[0].real)
    return multiplicities


def commutant_dimension(multiplicities: list[int]) -> int:
    return sum(value * value for value in multiplicities)


def wedderburn_signature(multiplicities: list[int], all_irreps: list[Irrep]) -> tuple[tuple[int, int], ...]:
    """Unitary-conjugacy signature of the representation commutant."""
    return tuple(sorted(
        (multiplicity, target.dimension)
        for multiplicity, target in zip(multiplicities, all_irreps)
        if multiplicity
    ))


def search() -> dict[str, object]:
    all_irreps = irreps()
    for i, left in enumerate(all_irreps):
        for j, right in enumerate(all_irreps):
            expected = 1 if i == j else 0
            assert inner(left.values, right.values) == expected

    coefficients: list[tuple[str, tuple[complex, ...], int]] = []
    for irrep in all_irreps:
        coefficients.append((irrep.label, irrep.values, irrep.dimension))
    for left_index, right_index in combinations_with_replacement(range(len(all_irreps)), 2):
        left = all_irreps[left_index]
        right = all_irreps[right_index]
        values = tuple(a + b for a, b in zip(left.values, right.values))
        coefficients.append((left.label + "+" + right.label, values, left.dimension + right.dimension))

    scored = []
    coefficient_profiles = []
    for label, values, dimension in coefficients:
        by_character: dict[Bit3, list[int]] = {}
        for source in all_irreps:
            expansion = commutant_dimension(fusion(source, values, all_irreps))
            by_character.setdefault(source.character, []).append(expansion)
        forbidden_min = min(by_character[FORBIDDEN])
        allowed_max = max(max(by_character[character]) for character in ALLOWED_J_MINUS)
        allowed_sum = sum(sum(by_character[character]) for character in ALLOWED_J_MINUS)
        score = (forbidden_min - allowed_max, forbidden_min, -allowed_sum, -dimension)
        scored.append((score, label, dimension, by_character))
        coefficient_profiles.append((label, dimension, by_character))
    scored.sort(reverse=True, key=lambda item: item[0])

    best = []
    for score, label, dimension, by_character in scored[:24]:
        best.append(
            {
                "coefficient": label,
                "coefficient_dimension": dimension,
                "score_forbidden_min_minus_allowed_max": score[0],
                "expansion_by_j_minus_character": {
                    "".join(map(str, character)): sorted(by_character[character])
                    for character in (*ALLOWED_J_MINUS, FORBIDDEN)
                },
            }
        )

    perfect = [entry for entry in best if entry["score_forbidden_min_minus_allowed_max"] > 0]

    same_capacity_detectors = []
    for left_index in range(len(coefficient_profiles)):
        left_label, left_dimension, left_profile = coefficient_profiles[left_index]
        for right_index in range(left_index + 1, len(coefficient_profiles)):
            right_label, right_dimension, right_profile = coefficient_profiles[right_index]
            if left_dimension != right_dimension:
                continue
            left_allowed = tuple(
                sorted(left_profile[character]) for character in ALLOWED_J_MINUS
            )
            right_allowed = tuple(
                sorted(right_profile[character]) for character in ALLOWED_J_MINUS
            )
            if left_allowed != right_allowed:
                continue
            left_forbidden = sorted(left_profile[FORBIDDEN])
            right_forbidden = sorted(right_profile[FORBIDDEN])
            if left_forbidden == right_forbidden:
                continue
            gap = sum(left_forbidden) - sum(right_forbidden)
            if gap < 0:
                left_label, right_label = right_label, left_label
                left_forbidden, right_forbidden = right_forbidden, left_forbidden
                gap = -gap
            same_capacity_detectors.append(
                {
                    "higher_forbidden_coefficient": left_label,
                    "lower_forbidden_coefficient": right_label,
                    "coefficient_dimension": left_dimension,
                    "allowed_profiles": {
                        "".join(map(str, character)): sorted(left_profile[character])
                        for character in ALLOWED_J_MINUS
                    },
                    "higher_forbidden_profile": left_forbidden,
                    "lower_forbidden_profile": right_forbidden,
                    "total_forbidden_commutant_gap": gap,
                }
            )
    same_capacity_detectors.sort(
        key=lambda item: (
            item["total_forbidden_commutant_gap"],
            -item["coefficient_dimension"],
        ),
        reverse=True,
    )

    # Exhaust every coefficient with exactly three irreducible summands.  The
    # fusion tensor makes this an integer-only search: fusion multiplicities
    # add, then the commutant dimension is their squared l2 norm.
    fusion_tensor = [
        [fusion(source, coefficient.values, all_irreps) for coefficient in all_irreps]
        for source in all_irreps
    ]
    character_source_indices = {
        character: [
            index for index, irrep in enumerate(all_irreps) if irrep.character == character
        ]
        for character in (*ALLOWED_J_MINUS, FORBIDDEN)
    }
    seen_three: dict[tuple[object, ...], tuple[tuple[int, ...], tuple[int, int, int]]] = {}
    three_detectors = []
    three_count = 0
    for coefficient_indices in combinations_with_replacement(range(len(all_irreps)), 3):
        three_count += 1
        coefficient_dimension = sum(all_irreps[index].dimension for index in coefficient_indices)
        profiles: dict[Bit3, tuple[int, ...]] = {}
        for character, source_indices in character_source_indices.items():
            expansion_values = []
            for source_index in source_indices:
                multiplicities = [
                    sum(fusion_tensor[source_index][coefficient_index][target_index]
                        for coefficient_index in coefficient_indices)
                    for target_index in range(len(all_irreps))
                ]
                expansion_values.append(commutant_dimension(multiplicities))
            profiles[character] = tuple(sorted(expansion_values))
        allowed_key: tuple[object, ...] = (
            coefficient_dimension,
            *(profiles[character] for character in ALLOWED_J_MINUS),
        )
        previous = seen_three.get(allowed_key)
        if previous is None:
            seen_three[allowed_key] = (profiles[FORBIDDEN], coefficient_indices)
            continue
        previous_forbidden, previous_indices = previous
        if previous_forbidden == profiles[FORBIDDEN]:
            continue
        previous_sum = sum(previous_forbidden)
        current_sum = sum(profiles[FORBIDDEN])
        if previous_sum >= current_sum:
            high_indices, low_indices = previous_indices, coefficient_indices
            high_forbidden, low_forbidden = previous_forbidden, profiles[FORBIDDEN]
        else:
            high_indices, low_indices = coefficient_indices, previous_indices
            high_forbidden, low_forbidden = profiles[FORBIDDEN], previous_forbidden
        three_detectors.append(
            {
                "higher_forbidden_coefficient": "+".join(all_irreps[index].label for index in high_indices),
                "lower_forbidden_coefficient": "+".join(all_irreps[index].label for index in low_indices),
                "coefficient_dimension": coefficient_dimension,
                "allowed_profiles": {
                    "".join(map(str, character)): list(profiles[character])
                    for character in ALLOWED_J_MINUS
                },
                "higher_forbidden_profile": list(high_forbidden),
                "lower_forbidden_profile": list(low_forbidden),
                "total_forbidden_commutant_gap": abs(previous_sum - current_sum),
            }
        )
    three_detectors.sort(
        key=lambda item: (item["total_forbidden_commutant_gap"], -item["coefficient_dimension"]),
        reverse=True,
    )

    # For larger sparse coefficients use the character formula directly.
    # For a fixed source T_k, End(T_k tensor V) is the quadratic form with
    # Gram entries <chi_T chi_i, chi_T chi_j>.  Absolute source characters are
    # independent of the radical label, so one representative per central
    # character suffices.
    source_representatives = {
        character: next(irrep for irrep in all_irreps if irrep.character == character)
        for character in (*ALLOWED_J_MINUS, FORBIDDEN)
    }
    fusion_grams: dict[Bit3, list[list[int]]] = {}
    for character, source in source_representatives.items():
        twisted = [tensor_values(source.values, coefficient.values) for coefficient in all_irreps]
        fusion_grams[character] = [
            [inner(left, right) for right in twisted] for left in twisted
        ]

    def quadratic_profile(indices: tuple[int, ...], character: Bit3) -> int:
        gram = fusion_grams[character]
        return sum(gram[left][right] for left in indices for right in indices)

    sparse_detector_counts = {}
    sparse_best = {}
    for summand_count in (4, 5):
        seen: dict[tuple[int, int, int, int], tuple[int, tuple[int, ...]]] = {}
        detectors = []
        coefficient_count = 0
        for indices in combinations_with_replacement(range(len(all_irreps)), summand_count):
            coefficient_count += 1
            dimension = sum(all_irreps[index].dimension for index in indices)
            allowed_values = tuple(
                quadratic_profile(indices, character) for character in ALLOWED_J_MINUS
            )
            key = (dimension, *allowed_values)
            forbidden_value = quadratic_profile(indices, FORBIDDEN)
            previous = seen.get(key)
            if previous is None:
                seen[key] = (forbidden_value, indices)
                continue
            previous_forbidden, previous_indices = previous
            if previous_forbidden == forbidden_value:
                continue
            if previous_forbidden >= forbidden_value:
                high_indices, low_indices = previous_indices, indices
                high_value, low_value = previous_forbidden, forbidden_value
            else:
                high_indices, low_indices = indices, previous_indices
                high_value, low_value = forbidden_value, previous_forbidden
            detectors.append(
                {
                    "higher_forbidden_coefficient": "+".join(all_irreps[index].label for index in high_indices),
                    "lower_forbidden_coefficient": "+".join(all_irreps[index].label for index in low_indices),
                    "coefficient_dimension": dimension,
                    "allowed_values": {
                        "".join(map(str, character)): value
                        for character, value in zip(ALLOWED_J_MINUS, allowed_values)
                    },
                    "higher_forbidden_value": high_value,
                    "lower_forbidden_value": low_value,
                    "forbidden_gap": high_value - low_value,
                }
            )
        detectors.sort(
            key=lambda item: (item["forbidden_gap"], -item["coefficient_dimension"]),
            reverse=True,
        )
        sparse_detector_counts[str(summand_count)] = {
            "coefficient_count": coefficient_count,
            "detector_count": len(detectors),
        }
        sparse_best[str(summand_count)] = detectors[:16]

    allowed_source_indices = [
        index
        for index, irrep in enumerate(all_irreps)
        if irrep.character in ALLOWED_J_MINUS
    ]
    forbidden_source_index = next(
        index for index, irrep in enumerate(all_irreps) if irrep.character == FORBIDDEN
    )

    def coefficient_fusion(indices: tuple[int, ...], source_index: int) -> list[int]:
        return [
            sum(fusion_tensor[source_index][coefficient_index][target_index]
                for coefficient_index in indices)
            for target_index in range(len(all_irreps))
        ]

    def allowed_wedderburn_key(indices: tuple[int, ...]) -> tuple[object, ...]:
        return (
            sum(all_irreps[index].dimension for index in indices),
            *(
                wedderburn_signature(coefficient_fusion(indices, source_index), all_irreps)
                for source_index in allowed_source_indices
            ),
        )

    seen_wedderburn: dict[bytes, tuple[tuple[int, ...], tuple[tuple[int, int], ...]]] = {}
    wedderburn_detectors = []
    for indices in combinations_with_replacement(range(len(all_irreps)), 4):
        key = allowed_wedderburn_key(indices)
        digest = hashlib.blake2b(repr(key).encode("ascii"), digest_size=16).digest()
        forbidden_signature = wedderburn_signature(
            coefficient_fusion(indices, forbidden_source_index), all_irreps
        )
        previous = seen_wedderburn.get(digest)
        if previous is None:
            seen_wedderburn[digest] = (indices, forbidden_signature)
            continue
        previous_indices, previous_forbidden = previous
        if previous_forbidden == forbidden_signature:
            continue
        if allowed_wedderburn_key(previous_indices) != key:
            continue
        wedderburn_detectors.append(
            {
                "first_coefficient": "+".join(all_irreps[index].label for index in previous_indices),
                "second_coefficient": "+".join(all_irreps[index].label for index in indices),
                "coefficient_dimension": key[0],
                "allowed_wedderburn_signatures_equal": True,
                "first_forbidden_signature": previous_forbidden,
                "second_forbidden_signature": forbidden_signature,
                "first_forbidden_commutant_dimension": sum(m * m for m, _ in previous_forbidden),
                "second_forbidden_commutant_dimension": sum(m * m for m, _ in forbidden_signature),
            }
        )
        if len(wedderburn_detectors) >= 32:
            break

    packet_automorphisms = packet_linear_automorphisms()
    coefficient_swap_automorphisms = []
    for row_change, column_change, center_change in packet_automorphisms:
        character_action = transpose3(center_change)
        if mat3_vec(character_action, (0, 1, 1)) != (1, 0, 1):
            continue
        coefficient_swap_automorphisms.append(
            {
                "p_change": [list(row) for row in row_change],
                "q_change": [list(row) for row in column_change],
                "center_change": [list(row) for row in center_change],
                "character_action": {
                    "011": "".join(map(str, mat3_vec(character_action, (0, 1, 1)))),
                    "100": "".join(map(str, mat3_vec(character_action, (1, 0, 0)))),
                    "101": "".join(map(str, mat3_vec(character_action, (1, 0, 1)))),
                    "110": "".join(map(str, mat3_vec(character_action, (1, 1, 0)))),
                    "111": "".join(map(str, mat3_vec(character_action, (1, 1, 1)))),
                },
            }
        )

    trivial_index = next(index for index, irrep in enumerate(all_irreps) if irrep.label == "000:0000")
    type_011_index = next(index for index, irrep in enumerate(all_irreps) if irrep.label == "011:")
    type_101_index = next(index for index, irrep in enumerate(all_irreps) if irrep.label == "101:")
    canonical_plus = (trivial_index, trivial_index, trivial_index, type_011_index)
    canonical_minus = (trivial_index, trivial_index, trivial_index, type_101_index)

    def source_signatures(indices: tuple[int, ...], character: Bit3) -> list[tuple[tuple[int, int], ...]]:
        return [
            wedderburn_signature(coefficient_fusion(indices, source_index), all_irreps)
            for source_index, source in enumerate(all_irreps)
            if source.character == character
        ]

    canonical_allowed = {}
    for character in ALLOWED_J_MINUS:
        plus_signatures = source_signatures(canonical_plus, character)
        minus_signatures = source_signatures(canonical_minus, character)
        assert plus_signatures == minus_signatures
        canonical_allowed["".join(map(str, character))] = plus_signatures
    canonical_plus_forbidden = source_signatures(canonical_plus, FORBIDDEN)
    canonical_minus_forbidden = source_signatures(canonical_minus, FORBIDDEN)
    assert canonical_plus_forbidden != canonical_minus_forbidden
    return {
        "group_order": 128,
        "irrep_count": len(all_irreps),
        "sum_dimension_squares": sum(irrep.dimension**2 for irrep in all_irreps),
        "coefficient_count": len(coefficients),
        "perfect_forbidden_detectors_in_top_24": len(perfect),
        "best_candidates": best,
        "same_capacity_forbidden_detector_count": len(same_capacity_detectors),
        "best_same_capacity_forbidden_detectors": same_capacity_detectors[:24],
        "three_summand_coefficient_count": three_count,
        "three_summand_forbidden_detector_count": len(three_detectors),
        "best_three_summand_forbidden_detectors": three_detectors[:24],
        "sparse_same_capacity_detector_counts": sparse_detector_counts,
        "best_sparse_same_capacity_detectors": sparse_best,
        "four_summand_wedderburn_detector_count_before_cutoff": len(wedderburn_detectors),
        "four_summand_wedderburn_detectors": wedderburn_detectors,
        "packet_linear_automorphism_count": len(packet_automorphisms),
        "coefficient_011_to_101_automorphism_count": len(coefficient_swap_automorphisms),
        "coefficient_011_to_101_automorphisms": coefficient_swap_automorphisms[:24],
        "canonical_covariant_wedderburn_detector": {
            "plus_coefficient": "3*000:0000 + 011:",
            "minus_coefficient": "3*000:0000 + 101:",
            "coefficient_dimension": 7,
            "allowed_signatures": canonical_allowed,
            "plus_forbidden_signature": canonical_plus_forbidden,
            "minus_forbidden_signature": canonical_minus_forbidden,
            "amplified_normalized_reynolds_distance_lower_bound": "1/49",
        },
    }


if __name__ == "__main__":
    print(json.dumps(search(), indent=2, sort_keys=True))
