"""Test the eventual-zero germ quotient of every hard atlas prefix pair.

The six-cylinder support component

    000, 010, 10

gives the three eventually-zero rays ``0^infinity``, ``010^infinity`` and
``10^infinity``.  On such a ray, appending a zero to its cylinder prefix does
not change the ray, whereas the complementary one-child cylinder misses it.
If a hard pair and its stars preserve the span of these three rays, their
restriction is a finite star representation which rules out a second child
equivalence at every word depth.
"""

import json
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, "experiments")

from atlas_survivor_infinite_projection import (  # noqa: E402
    certify_pair,
    hard_pairs,
)
from atlas_raw_compressor_proper_infinite import raw_and_comb  # noqa: E402
from atlas_survivor_prefix_obstruction import (  # noqa: E402
    cylinder_projection,
    leavitt_star,
)
from atlas_two_chart_search import leavitt_chart_element  # noqa: E402


RAY_STATES = ((), (0, 1), (1,))


def canonical_eventual_zero(prefix):
    prefix = tuple(prefix)
    while prefix and prefix[-1] == 0:
        prefix = prefix[:-1]
    return prefix


def monomial_on_eventual_zero(left, right, state):
    for index, bit in enumerate(right):
        expected = state[index] if index < len(state) else 0
        if bit != expected:
            return None
    suffix = state[len(right):] if len(right) < len(state) else ()
    return canonical_eventual_zero(tuple(left) + suffix)


def restricted_matrix(value):
    index_of = {state: index for index, state in enumerate(RAY_STATES)}
    size = len(RAY_STATES)
    matrix = [[0 for _ in range(size)] for _ in range(size)]
    outside = set()
    for column, state in enumerate(RAY_STATES):
        outputs = set()
        for (left, right), coefficient in value.items():
            if not coefficient & 1:
                continue
            target = monomial_on_eventual_zero(left, right, state)
            if target is None:
                continue
            if target in outputs:
                outputs.remove(target)
            else:
                outputs.add(target)
        for target in outputs:
            row = index_of.get(target)
            if row is None:
                outside.add(target)
            else:
                matrix[row][column] ^= 1
    return matrix, sorted("".join(map(str, state)) or "0^infinity"
                          for state in outside)


def transpose(matrix):
    return [list(row) for row in zip(*matrix)]


def multiply(first, second):
    size = len(first)
    return [[sum(first[row][middle] * second[middle][column]
                 for middle in range(size)) & 1
             for column in range(size)]
            for row in range(size)]


def identity(size):
    return [[int(row == column) for column in range(size)]
            for row in range(size)]


def projection_rank(matrix):
    work = [row[:] for row in matrix]
    rank = 0
    column_count = len(work[0]) if work else 0
    for column in range(column_count):
        pivot = next((row for row in range(rank, len(work))
                      if work[row][column]), None)
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        for row in range(len(work)):
            if row != rank and work[row][column]:
                work[row] = [left ^ right
                             for left, right in zip(work[row], work[rank])]
        rank += 1
    return rank


def main():
    results = []
    for pair_index, (boundary_index, inverted, rotation, prefix_length,
                     q, letter) in enumerate(hard_pairs()):
        certificate = certify_pair(q, letter)
        generator_data = {}
        reducing = True
        star_compatible = True
        unitary = True
        for name, value in (("q", q), ("l", letter)):
            matrix, outside = restricted_matrix(value)
            star_matrix, star_outside = restricted_matrix(leavitt_star(value))
            generator_data[name] = {
                "matrix": matrix,
                "outside": outside,
                "star_matrix": star_matrix,
                "star_outside": star_outside,
            }
            reducing &= not outside and not star_outside
            star_compatible &= star_matrix == transpose(matrix)
            unitary &= (multiply(star_matrix, matrix) == identity(3)
                        and multiply(matrix, star_matrix) == identity(3))

        base = certificate["infinite_projection"]
        zero_child = certificate["proper_equivalent_child"]
        one_child = certificate["nonzero_complement"]
        base_matrix, base_outside = restricted_matrix(cylinder_projection(base))
        zero_matrix, zero_outside = restricted_matrix(
            cylinder_projection(zero_child))
        one_matrix, one_outside = restricted_matrix(
            cylinder_projection(one_child))
        if base_outside or zero_outside or one_outside:
            raise AssertionError("a cylinder projection left the ray sector")

        results.append({
            "pair_index": pair_index,
            "boundary_index": boundary_index,
            "inverted": inverted,
            "rotation": rotation,
            "prefix_length": prefix_length,
            "ray_states": ["".join(map(str, state)) or "0^infinity"
                           for state in RAY_STATES],
            "reducing": reducing,
            "star_compatible": star_compatible,
            "unitary": unitary,
            "generators": generator_data,
            "base": base,
            "zero_child": zero_child,
            "one_child": one_child,
            "base_rank": projection_rank(base_matrix),
            "zero_child_rank": projection_rank(zero_matrix),
            "one_child_rank": projection_rank(one_matrix),
            "base_equals_zero_child": base_matrix == zero_matrix,
            "one_child_is_zero": one_matrix == [[0] * 3 for _ in range(3)],
        })

    compressor_data = {}
    raw, comb = raw_and_comb()
    for name, value in (("raw", raw), ("comb", comb)):
        matrix, outside = restricted_matrix(value)
        star_matrix, star_outside = restricted_matrix(leavitt_star(value))
        compressor_data[name] = {
            "matrix": matrix,
            "outside": outside,
            "star_matrix": star_matrix,
            "star_outside": star_outside,
            "reducing": not outside and not star_outside,
            "star_compatible": star_matrix == transpose(matrix),
        }

    source_payload = json.loads(Path(
        "experiments/atlas-raw-compressor-source-words.json"
    ).read_text(encoding="utf-8"))
    source_syllable_data = {}
    for family in ("raw", "comb"):
        distinct = {}
        for position, item in enumerate(source_payload[f"{family}_source_word"]):
            key = (item["factor"], item["matrix_f2_hex"])
            distinct.setdefault(key, []).append(position)
        breakers = []
        for (factor, matrix_hex), positions in distinct.items():
            matrix = np.frombuffer(bytes.fromhex(matrix_hex),
                                   dtype=np.uint8).reshape(4, 4).copy()
            value = leavitt_chart_element(factor, matrix)
            restricted, outside = restricted_matrix(value)
            restricted_star, star_outside = restricted_matrix(
                leavitt_star(value))
            if outside or star_outside:
                breakers.append({
                    "factor": factor,
                    "matrix_f2_hex": matrix_hex,
                    "positions": positions,
                    "outside": outside,
                    "star_outside": star_outside,
                    "restricted_inside_part": restricted,
                    "restricted_star_inside_part": restricted_star,
                })
        source_syllable_data[family] = {
            "distinct_syllables": len(distinct),
            "germ_breaker_count": len(breakers),
            "germ_breakers": breakers,
        }

    print(json.dumps({
        "pair_count": len(results),
        "all_reducing": all(result["reducing"] for result in results),
        "all_star_compatible": all(
            result["star_compatible"] for result in results),
        "all_unitary": all(result["unitary"] for result in results),
        "all_base_rank_positive": all(
            result["base_rank"] > 0 for result in results),
        "all_base_equals_zero_child": all(
            result["base_equals_zero_child"] for result in results),
        "all_one_child_zero": all(
            result["one_child_is_zero"] for result in results),
        "compressors": compressor_data,
        "compressor_source_syllables": source_syllable_data,
        "results": results,
    }, indent=2))


if __name__ == "__main__":
    main()
