"""Certify the finite subgroup carried by each actual hard prefix.

The classical fold puts a hard prefix beside the raw ``K ~= S3`` inside an
``S4``.  This replay does not use the fold.  It evaluates the original
cross-chart prefix in the binary Leavitt algebra and closes that actual unit
together with the two raw second-chart generators.

The inverse of a prefix is obtained by reversing its source word and
inverting every chart matrix.  The Leavitt transpose ``q*`` is treated as a
separate group unit; it is never substituted for the group inverse.
"""

from collections import Counter
import json
import sys

import numpy as np

sys.path.insert(0, "experiments")

from atlas_kernel_collision_enumerator import ONE  # noqa: E402
from atlas_raw_compressor_amalgam_audit import decode_word  # noqa: E402
from atlas_survivor_infinite_projection import HARD_CASES  # noqa: E402
from atlas_survivor_prefix_gallery import (  # noqa: E402
    oriented_rotations,
    survivor_representatives,
)
from atlas_survivor_prefix_obstruction import (  # noqa: E402
    leavitt_is_zero,
    leavitt_star,
)
from atlas_two_chart_search import (  # noqa: E402
    gf2_inv,
    leavitt_add,
    leavitt_chart_element,
    leavitt_mul,
    matrix_key,
)


def equal(left, right):
    return leavitt_is_zero(leavitt_add(left, right))


def product(values):
    result = ONE
    for value in values:
        result = leavitt_mul(result, value)
    return result


def evaluate(word):
    return product(leavitt_chart_element(factor, matrix)
                   for factor, matrix in word)


def inverse_word(word):
    return [(factor, gf2_inv(matrix))
            for factor, matrix in reversed(word)]


def contains(elements, candidate):
    return any(equal(element, candidate) for element in elements)


def closure(generators, limit=256):
    elements = [ONE]
    frontier = [ONE]
    while frontier:
        current = frontier.pop()
        for generator in generators:
            candidate = leavitt_mul(current, generator)
            if contains(elements, candidate):
                continue
            elements.append(candidate)
            frontier.append(candidate)
            if len(elements) > limit:
                raise AssertionError("finite-packet closure exceeded limit")
    return elements


def element_order(value, limit=256):
    running = ONE
    for exponent in range(1, limit + 1):
        running = leavitt_mul(running, value)
        if equal(running, ONE):
            return exponent
    raise AssertionError("element order exceeded finite audit bound")


def inverse_from_order(value):
    return product([value] * (element_order(value) - 1))


def order_histogram(elements):
    return dict(sorted(Counter(element_order(value)
                               for value in elements).items()))


def core_order(subgroup, ambient):
    core = []
    for element in subgroup:
        if all(contains(
                subgroup,
                product([conjugator, element,
                         inverse_from_order(conjugator)]))
               for conjugator in ambient):
            core.append(element)
    return len(core)


def raw_k_generators():
    with open("experiments/atlas-raw-compressor-source-words.json",
              "r", encoding="utf-8") as stream:
        source = json.load(stream)
    raw = decode_word(source["raw_source_word"])
    distinct = {}
    for factor, matrix in raw:
        if factor == 2:
            distinct.setdefault(matrix_key(matrix), matrix)
    if len(distinct) != 2:
        raise AssertionError("raw second chart no longer has two generators")
    words = [[(2, matrix)] for _key, matrix in sorted(distinct.items())]
    generators = [evaluate(word) for word in words]
    inverses = [evaluate(inverse_word(word)) for word in words]
    packet = closure([*generators, *inverses])
    if len(packet) != 6 or order_histogram(packet) != {1: 1, 2: 3, 3: 2}:
        raise AssertionError("actual raw K is not S3")
    return generators, inverses, packet


def distinct_hard_prefixes():
    prefixes = []
    for boundary_index, representative in survivor_representatives():
        lookup = {
            (inverted, rotation): prefix_length
            for inverted, rotation, prefix_length in HARD_CASES[boundary_index]
        }
        for inverted, rotation, word in oriented_rotations(representative):
            prefix_length = lookup.get((inverted, rotation))
            if prefix_length is None:
                continue
            prefix_word = word[:prefix_length]
            value = evaluate(prefix_word)
            inverse = evaluate(inverse_word(prefix_word))
            if not equal(leavitt_mul(value, inverse), ONE):
                raise AssertionError("reversed source word is not an inverse")
            existing = next((item for item in prefixes
                             if equal(item["value"], value)), None)
            occurrence = {
                "boundary_index": boundary_index,
                "inverted": inverted,
                "rotation": rotation,
                "prefix_length": prefix_length,
            }
            if existing is None:
                prefixes.append({
                    "value": value,
                    "inverse": inverse,
                    "occurrences": [occurrence],
                })
            else:
                existing["occurrences"].append(occurrence)
    if len(prefixes) != 4:
        raise AssertionError("expected four distinct actual hard prefixes")
    return prefixes


def main():
    k_generators, k_inverses, k_packet = raw_k_generators()
    records = []
    for index, entry in enumerate(distinct_hard_prefixes()):
        q = entry["value"]
        q_inverse = entry["inverse"]
        q_star = leavitt_star(q)
        q_star_inverse = leavitt_star(q_inverse)

        s4 = closure([*k_generators, *k_inverses, q, q_inverse])
        s4_histogram = order_histogram(s4)
        k_core_order = core_order(k_packet, s4)
        if (len(s4) != 24 or
                s4_histogram != {1: 1, 2: 9, 3: 8, 4: 6} or
                k_core_order != 1):
            raise AssertionError("actual hard prefix does not extend K to S4")

        packet168 = closure([
            *k_generators, *k_inverses,
            q, q_inverse, q_star, q_star_inverse,
        ])
        packet168_histogram = order_histogram(packet168)
        expected168 = {1: 1, 2: 21, 3: 56, 4: 42, 7: 48}
        if len(packet168) != 168 or packet168_histogram != expected168:
            raise AssertionError("hard prefix/star packet is not order 168")

        records.append({
            "prefix_index": index,
            "occurrences": entry["occurrences"],
            "q_order": element_order(q),
            "q_star_equals_group_inverse": equal(q_star, q_inverse),
            "K_q_order": len(s4),
            "K_q_order_histogram": s4_histogram,
            "K_core_in_K_q_order": k_core_order,
            "K_q_isomorphic_to": "S4",
            "K_q_qstar_order": len(packet168),
            "K_q_qstar_order_histogram": packet168_histogram,
        })

    if [record["q_order"] for record in records] != [4, 2, 4, 2]:
        raise AssertionError("hard-prefix order sequence changed")
    if any(record["q_star_equals_group_inverse"] for record in records):
        raise AssertionError("Leavitt star unexpectedly became group inverse")

    print(json.dumps({
        "raw_K_order": 6,
        "raw_K_isomorphic_to": "S3",
        "distinct_actual_hard_prefixes": len(records),
        "true_inverse_method": "reverse word and invert each chart matrix",
        "leavitt_star_role": "separate group word, not group inverse",
        "records": records,
    }, indent=2))


if __name__ == "__main__":
    main()
