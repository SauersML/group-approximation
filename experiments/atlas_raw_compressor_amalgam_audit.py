"""Audit the raw packet in the classical ``A8 *_H A8`` boundary branch.

This is a fast falsification test for a direct spherical compression.  A word
which normalizes the overlap ``H=diag(GL(3,2),1)`` gives a closed operator on
the fixed nonincident-flag edge type.  A word which does not normalize ``H``
is only a transport between different conjugate edge types; its individual
35/56 spherical blocks cannot be treated as a closed holonomy.
"""

import json
import sys

import numpy as np

sys.path.insert(0, "experiments")

from atlas_boundary_amalgam_normal_form import (  # noqa: E402
    amalgam_normal_form,
    lies_in_h,
    record_normal_form,
    transported_word,
)
from atlas_boundary_group_algebra_audit import matrix_from_key  # noqa: E402
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX  # noqa: E402
from atlas_certified_a8_alignment import boundary_words  # noqa: E402
from atlas_two_chart_search import (  # noqa: E402
    gf2_inv,
    matrix_key,
    product,
    transvection,
)


def decode_word(encoded):
    return [
        (
            item["factor"],
            np.frombuffer(bytes.fromhex(item["matrix_f2_hex"]),
                          dtype=np.uint8).reshape(4, 4).copy(),
        )
        for item in encoded
    ]


def inverse_word(word):
    return [(factor, gf2_inv(matrix))
            for factor, matrix in reversed(word)]


def conjugate_word(word, h):
    return product(word, [(1, h)], inverse_word(word))


def in_literal_h(normal):
    return (not normal or
            (len(normal) == 1 and lies_in_h(normal[0][1])))


def normalizer_audit(word):
    generators = [transvection(i, j) for i, j in
                  ((0, 1), (1, 0), (1, 2), (2, 1))]
    conjugates = []
    for generator in generators:
        normal = amalgam_normal_form(conjugate_word(word, generator))
        conjugates.append({
            "h_generator_hex": matrix_key(generator).hex(),
            "normal_form": record_normal_form(normal),
            "returns_to_H": in_literal_h(normal),
        })
    return {
        "tested_H_generators": len(generators),
        "returned_to_H": sum(item["returns_to_H"] for item in conjugates),
        "normalizes_H_on_test_generators": all(
            item["returns_to_H"] for item in conjugates),
        "conjugates": conjugates,
    }


def main():
    with open("experiments/atlas-raw-compressor-source-words.json",
              "r", encoding="utf-8") as stream:
        source = json.load(stream)

    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)

    raw = transported_word(
        decode_word(source["raw_source_word"]),
        alignment, alignment_inverse)
    comb = transported_word(
        decode_word(source["comb_source_word"]),
        alignment, alignment_inverse)

    # The first certified hard pair is class 11, forward rotation zero, with
    # prefix length two and the third syllable as its next letter.
    class11 = transported_word(
        boundary_words()[11], alignment, alignment_inverse)
    hard_prefix = class11[:2]
    hard_letter = class11[2:3]

    records = {}
    for name, word in (
        ("raw", raw),
        ("comb", comb),
        ("hard_class11_prefix", hard_prefix),
        ("hard_class11_next_letter", hard_letter),
    ):
        normal = amalgam_normal_form(word)
        records[name] = {
            "source_syllables": len(word),
            "amalgam_normal_length": len(normal),
            "amalgam_normal_form": record_normal_form(normal),
            "normalizer_audit": normalizer_audit(word),
        }

    print(json.dumps({
        "candidate": "A8 *_H A8",
        "alignment_hex": INNER_ALIGNMENT_HEX,
        "H_generators": "E01,E10,E12,E21",
        "records": records,
    }, indent=2))


if __name__ == "__main__":
    main()
