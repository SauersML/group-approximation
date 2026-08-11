"""Classify the live atlas relators under all abstract factor symmetries.

Aut(A8)=S8 is generated, in the GL(4,2) model, by inner automorphisms and the
graph automorphism g -> (g^-1)^T.  We allow these automorphisms independently
on the two free factors, interchange the factors, and compare cyclic rotations
of a word and its inverse.  The calculation is exact over F_2.
"""

import json
import sys

sys.path.insert(0, "experiments")

from atlas_boundary_inner_alignment import enumerate_gl4  # noqa: E402
from atlas_kernel_collision_enumerator import (  # noqa: E402
    enumerate_ball,
    factor_projections,
    spanning_tree_kernel_words,
)
from atlas_perfect_overlap_scan import cardinality_obstruction  # noqa: E402
from atlas_survivor_conjugacy import (  # noqa: E402
    cyclic_reduce,
    invert_word,
    oriented_key,
    unoriented_key,
)
from atlas_two_chart_search import (  # noqa: E402
    I4,
    gf2_inv,
    gf2_mul,
    matrix_key,
)


def rotations(word):
    return [word[offset:] + word[:offset] for offset in range(len(word))]


def main():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    identity_key = matrix_key(I4)
    boundary = [word for word in words if any(
        matrix_key(projection) != identity_key
        for projection in factor_projections(word))]
    classes = {}
    for boundary_index, word in enumerate(boundary):
        if not cardinality_obstruction(word)[
                "positive_cardinality_obstruction_rows"]:
            continue
        classes.setdefault(unoriented_key(word), {
            "boundary_index": boundary_index,
            "word": cyclic_reduce(word),
        })
    if len(classes) != 4:
        raise AssertionError("survivor conjugacy classification changed")

    variants_by_class = []
    sequences = set()
    matrices = {}
    records = list(classes.values())
    for record in records:
        word = record["word"]
        variants = []
        for oriented in (word, invert_word(word)):
            for variant in rotations(oriented):
                pair = []
                for factor in (1, 2):
                    sequence = tuple(
                        matrix_key(matrix) for current, matrix in variant
                        if current == factor)
                    sequences.add(sequence)
                    pair.append(sequence)
                variants.append(tuple(pair))
                for _factor, matrix in variant:
                    matrices.setdefault(matrix_key(matrix), matrix)
        variants_by_class.append(variants)

    canonical = {sequence: None for sequence in sequences}
    automorphisms_tested = 0
    for outer in (False, True):
        for conjugator in enumerate_gl4():
            automorphisms_tested += 1
            conjugator_inverse = gf2_inv(conjugator)
            images = {}
            for key, original in matrices.items():
                matrix = (gf2_inv(original).T.copy()
                          if outer else original)
                images[key] = matrix_key(gf2_mul(gf2_mul(
                    conjugator, matrix), conjugator_inverse))
            for sequence in sequences:
                image = tuple(images[key] for key in sequence)
                if canonical[sequence] is None or image < canonical[sequence]:
                    canonical[sequence] = image

    signatures = []
    for variants in variants_by_class:
        candidates = []
        for first, second in variants:
            signature = (canonical[first], canonical[second])
            candidates.extend((signature, tuple(reversed(signature))))
        signatures.append(min(candidates))
    if len(set(signatures)) != 1:
        raise AssertionError("the four survivor types split into several orbits")

    key_to_class = {
        unoriented_key(record["word"]): index
        for index, record in enumerate(records)
    }
    actual_actions = []
    for name, use_outer, swap_factors in (
            ("prefix_chart_swap", False, True),
            ("adjoint_inverse", True, False),
            ("adjoint_inverse_after_swap", True, True)):
        images = []
        for record in records:
            transformed = []
            for factor, original in record["word"]:
                matrix = (gf2_inv(original).T.copy()
                          if use_outer else original)
                transformed.append((
                    3 - factor if swap_factors else factor,
                    matrix,
                ))
            target = key_to_class[unoriented_key(transformed)]
            orientation = (1 if oriented_key(transformed) == oriented_key(
                records[target]["word"]) else -1)
            if orientation != 1:
                raise AssertionError("an atlas symmetry reverses orientation")
            images.append({
                "source": record["boundary_index"],
                "target": records[target]["boundary_index"],
                "orientation": orientation,
            })
        actual_actions.append({"name": name, "images": images})

    print(json.dumps({
        "survivor_conjugacy_classes": len(classes),
        "automorphisms_tested_per_factor": automorphisms_tested,
        "allow_factor_swap": True,
        "allow_word_inversion": True,
        "abstract_factor_automorphism_orbits": len(set(signatures)),
        "orbit_sizes": [len(signatures)],
        "actual_leavitt_symmetry_actions": actual_actions,
        "central_generators_after_inner_prefix_swap": 2,
    }, indent=2))


if __name__ == "__main__":
    main()
