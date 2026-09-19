"""Exhaust natural ``A11`` targets for the Atlas six-relator quotient.

Every nontrivial homomorphism ``A8 -> A11`` is a natural eight-point action
with three fixed points.  Fix the first chart.  The second labeled chart is
obtained by conjugating it by ``S11``; odd conjugators include the outer
automorphism.  Right multiplication by the pointwise centralizer ``S3`` of
the source chart does not change the second labeled chart, so the exact
candidate count is ``11!/3! = 6,652,800``.

Run under Sage on MSI.  All six words are read from the frozen exact
free-product-syllable artifact.  A survivor is a finite exact countermodel to
the five-row phase lift.
"""

import itertools
import json
import os
import time

import numpy as np

from atlas_a9_two_chart_scan import (
    exceptional_a8_map,
    inverse,
    multiply,
)


DEGREE = 11
RELATOR_ORDER = ("s_0", "s_11", "s_30", "s_44", "s_55", "c_19243")


def decode_words():
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-six-relator-relative-pieces.json"),
              "r", encoding="utf-8") as stream:
        record = json.load(stream)
    words = {}
    matrices = {}
    for name in RELATOR_ORDER:
        word = []
        for factor, value in record["relators"][name]["word"]:
            matrix = np.frombuffer(bytes.fromhex(value), dtype=np.uint8).reshape(4, 4)
            key = bytes(matrix.reshape(-1))
            matrices[key] = matrix
            word.append((factor, key))
        words[name] = word
    return words, list(matrices.values())


def conjugate(conjugator, value, conjugator_inverse):
    return multiply(multiply(conjugator, value), conjugator_inverse)


def evaluate(word, images, conjugator, conjugator_inverse, identity):
    value = identity
    cache = {}
    for factor, key in word:
        letter = images[key]
        if factor == 2:
            if key not in cache:
                cache[key] = conjugate(conjugator, letter, conjugator_inverse)
            letter = cache[key]
        value = multiply(value, letter)
    return value


def representatives():
    """One representative of ``S11/S3`` without enumerating all ``11!``."""
    positions = range(DEGREE)
    for fixed_preimages in itertools.combinations(positions, 3):
        moving_positions = [x for x in positions if x not in fixed_preimages]
        for moving_values in itertools.permutations(range(8)):
            value = [None] * DEGREE
            for source, target in zip(fixed_preimages, range(8, 11)):
                value[source] = target
            for source, target in zip(moving_positions, moving_values):
                value[source] = target
            yield tuple(value)


def main():
    words, matrices = decode_words()
    images = exceptional_a8_map(matrices, DEGREE)
    identity = tuple(range(DEGREE))
    tested = 0
    first_failure = {name: 0 for name in RELATOR_ORDER}
    survivors = []
    started = time.monotonic()

    for conjugator in representatives():
        tested += 1
        conjugator_inverse = inverse(conjugator)
        for name in RELATOR_ORDER:
            if evaluate(words[name], images, conjugator,
                        conjugator_inverse, identity) != identity:
                first_failure[name] += 1
                break
        else:
            survivors.append({
                "conjugator": [x + 1 for x in conjugator],
                "second_chart_fixed_points": [
                    conjugator_inverse[x] + 1 for x in range(8, 11)],
            })

    if tested != 6652800:
        raise AssertionError("S11/S3 representative count changed")
    print(json.dumps({
        "ambient": "A11 natural eight-point-support geometry",
        "candidate_classification": "all labeled nontrivial A8 -> A11 maps",
        "conjugators": "S11 modulo pointwise source-chart S3",
        "candidates_tested": tested,
        "relators": list(RELATOR_ORDER),
        "survivor_count": len(survivors),
        "survivors": survivors,
        "first_failure_histogram": first_failure,
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }, indent=2))


if __name__ == "__main__":
    main()
