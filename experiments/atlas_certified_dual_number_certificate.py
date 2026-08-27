"""Verify a finite central quotient of the certified radius-five atlas.

The target is ``GL(8, F_2[eps]/(eps^2))``.  Both atlas factors are copies
of the natural degree-eight permutation representation of ``A8``.  Their
relative alignment is deformed in the dual-number direction

    X = diag(1, 0, 0, 0, 0, 0, 1, 0).

Exact arithmetic verifies that the 24 certified-zero classes vanish and
that phase class 11 is the nontrivial central involution ``(1+eps) I``.
"""

from collections import deque
import json

import numpy as np

from atlas_certified_a8_alignment import (
    CERTIFIED_REPRESENTATIVE_INDICES,
    PHASE_INDEX,
    boundary_words,
)
from atlas_two_chart_search import I4, factor_generators, gf2_mul, matrix_key


ALIGNMENT_KEY = "00000100000100000100000000000001"
ALIGNMENT_PERMUTATION = (2, 7, 0, 5, 6, 3, 4, 1)
TANGENT_DIAGONAL_SUPPORT = (0, 6)

# These are the images under one fixed isomorphism GL(4,2) ~= A8 of the six
# standard transvections returned by ``factor_generators``.  Points are
# numbered from zero.  The table was obtained once by GAP's
# IsomorphismGroups(GL(4,2), AlternatingGroup(8)); all subsequent checks are
# self-contained finite arithmetic.
GENERATOR_IMAGES = {
    "01010000000100000000010000000001": (5, 3, 4, 1, 2, 0, 7, 6),
    "01000000010100000000010000000001": (1, 0, 4, 7, 2, 6, 5, 3),
    "01000000000101000000010000000001": (6, 5, 7, 4, 3, 1, 0, 2),
    "01000000000100000001010000000001": (6, 4, 3, 2, 1, 7, 0, 5),
    "01000000000100000000010100000001": (7, 3, 4, 1, 2, 6, 5, 0),
    "01000000000100000000010000000101": (5, 6, 4, 7, 2, 0, 1, 3),
}


def compose(left, right):
    """Compose permutations in the convention used by the atlas scripts."""
    return tuple(right[left[index]] for index in range(8))


def natural_a8_map():
    """Construct the fixed GL(4,2) ~= A8 map by exact breadth-first search."""
    source_generators = [word[0][1] for _, word in factor_generators()[:6]]
    target_generators = []
    for generator in source_generators:
        key = matrix_key(generator).hex()
        if key not in GENERATOR_IMAGES:
            raise AssertionError("the standard transvection table changed")
        target_generators.append(GENERATOR_IMAGES[key])

    identity_permutation = tuple(range(8))
    identity_key = matrix_key(I4).hex()
    images = {identity_key: identity_permutation}
    matrices = {identity_key: I4.copy()}
    queue = deque([identity_key])
    while queue:
        source_key = queue.popleft()
        source = matrices[source_key]
        source_image = images[source_key]
        for generator, generator_image in zip(
                source_generators, target_generators, strict=True):
            target = gf2_mul(source, generator)
            target_key = matrix_key(target).hex()
            # The GAP permutation convention is a right action, so the image
            # of source*generator is written in this reversed compose order.
            target_image = compose(generator_image, source_image)
            if target_key in images:
                if images[target_key] != target_image:
                    raise AssertionError("inconsistent A8 multiplication table")
                continue
            matrices[target_key] = target
            images[target_key] = target_image
            queue.append(target_key)

    if len(images) != 20160 or len(set(images.values())) != 20160:
        raise AssertionError("the natural A8 map is not an isomorphism")
    if images[ALIGNMENT_KEY] != ALIGNMENT_PERMUTATION:
        raise AssertionError("alignment image changed")
    return images


def permutation_matrix(permutation):
    matrix = np.zeros((8, 8), dtype=np.uint8)
    for source, target in enumerate(permutation):
        matrix[target, source] = 1
    return matrix


def f2_mul(left, right):
    return (left @ right) & 1


def pair_mul(left, right):
    """Multiply matrices over F_2[eps]/(eps^2)."""
    left_constant, left_tangent = left
    right_constant, right_tangent = right
    return (
        f2_mul(left_constant, right_constant),
        (f2_mul(left_constant, right_tangent)
         ^ f2_mul(left_tangent, right_constant)),
    )


def chart_images(images):
    identity = np.eye(8, dtype=np.uint8)
    zero = np.zeros((8, 8), dtype=np.uint8)
    alignment = permutation_matrix(images[ALIGNMENT_KEY])
    alignment_inverse = alignment.T.copy()
    tangent = np.zeros((8, 8), dtype=np.uint8)
    for index in TANGENT_DIAGONAL_SUPPORT:
        tangent[index, index] = 1

    first = {}
    second = {}
    for key, permutation in images.items():
        point_matrix = permutation_matrix(permutation)
        first[key] = (point_matrix, zero)
        constant = f2_mul(f2_mul(
            alignment, point_matrix), alignment_inverse)
        # Conjugation by (I+eps X) alignment.  Its inverse contains the
        # same tangent factor because the characteristic is two and X^2
        # is multiplied by eps^2=0.
        derivative = f2_mul(tangent, constant) ^ f2_mul(constant, tangent)
        second[key] = (constant, derivative)

    return first, second, identity, zero, tangent


def evaluate(word, first, second, identity, zero):
    value = (identity, zero)
    for factor, matrix in word:
        chart = first if factor == 1 else second
        value = pair_mul(value, chart[matrix_key(matrix).hex()])
    return value


def pair_equal(left, right):
    return np.array_equal(left[0], right[0]) and np.array_equal(
        left[1], right[1])


def f2_rank(rows):
    """Return the exact F_2-rank of a list of flattened binary matrices."""
    packed = []
    for row in rows:
        value = 0
        for entry in row:
            value = (value << 1) | int(entry)
        packed.append(value)
    rank = 0
    width = len(rows[0]) if rows else 0
    for bit in reversed(range(width)):
        pivot = next((index for index in range(rank, len(packed))
                      if (packed[index] >> bit) & 1), None)
        if pivot is None:
            continue
        packed[rank], packed[pivot] = packed[pivot], packed[rank]
        for index in range(len(packed)):
            if index != rank and ((packed[index] >> bit) & 1):
                packed[index] ^= packed[rank]
        rank += 1
    return rank


def main():
    images = natural_a8_map()
    first, second, identity, zero, tangent = chart_images(images)
    boundary = boundary_words()
    identity_pair = (identity, zero)
    phase_target = (identity, identity)

    zero_records = []
    for index in CERTIFIED_REPRESENTATIVE_INDICES:
        value = evaluate(boundary[index], first, second, identity, zero)
        if not pair_equal(value, identity_pair):
            raise AssertionError(f"certified class {index} did not vanish")
        zero_records.append({
            "boundary_index": index,
            "constant_is_identity": True,
            "tangent_is_zero": True,
        })

    phase = evaluate(boundary[PHASE_INDEX], first, second, identity, zero)
    if not pair_equal(phase, phase_target):
        raise AssertionError("phase is not (1+eps) I")
    if pair_equal(phase, identity_pair):
        raise AssertionError("phase unexpectedly vanished")
    if not pair_equal(pair_mul(phase, phase), identity_pair):
        raise AssertionError("phase does not have order two")

    # After reduction modulo eps, both charts generate the same A8.  Their
    # relative kernel is spanned by X + gXg^-1.  Since X is the diagonal
    # characteristic function of a two-set and A8 is two-transitive, this
    # is exactly the seven-dimensional even-weight diagonal module.
    kernel_directions = []
    for permutation in images.values():
        point_matrix = permutation_matrix(permutation)
        conjugate = f2_mul(f2_mul(
            point_matrix, tangent), point_matrix.T)
        direction = tangent ^ conjugate
        if np.any(direction ^ np.diag(np.diag(direction))):
            raise AssertionError("dual-number kernel direction is not diagonal")
        if int(np.diag(direction).sum()) % 2:
            raise AssertionError("dual-number kernel direction has odd weight")
        kernel_directions.append(direction.reshape(-1))
    kernel_rank = f2_rank(kernel_directions)
    if kernel_rank != 7:
        raise AssertionError("dual-number kernel is not the even-weight module")

    central_checks = 0
    for chart in (first, second):
        for _, word in factor_generators()[:6]:
            generator = chart[matrix_key(word[0][1]).hex()]
            if not pair_equal(
                    pair_mul(phase, generator), pair_mul(generator, phase)):
                raise AssertionError("phase is not central on a chart generator")
            central_checks += 1

    print(json.dumps({
        "source_group": "GL(4,2) ~= A8",
        "source_order": len(images),
        "natural_permutation_image_order": len(set(images.values())),
        "target": "GL(8, F2[eps]/(eps^2))",
        "coefficient_ring_cardinality": 4,
        "alignment_f2_hex": ALIGNMENT_KEY,
        "alignment_zero_based_permutation": ALIGNMENT_PERMUTATION,
        "tangent_diagonal_support_zero_based": TANGENT_DIAGONAL_SUPPORT,
        "alignment_tangent_rank_over_f2": len(TANGENT_DIAGONAL_SUPPORT),
        "image_structure": "(C2)^7 : A8",
        "image_kernel_dimension_over_f2": kernel_rank,
        "image_order": (2 ** kernel_rank) * len(images),
        "image_center_order": 2,
        "certified_zero_classes": zero_records,
        "phase_boundary_index": PHASE_INDEX,
        "phase_constant_is_identity": np.array_equal(phase[0], identity),
        "phase_tangent_is_identity": np.array_equal(phase[1], identity),
        "phase_is_nonidentity": not pair_equal(phase, identity_pair),
        "phase_order": 2,
        "phase_central_generator_checks": central_checks,
    }, indent=2))


if __name__ == "__main__":
    main()
