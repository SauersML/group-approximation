"""Search exact small chart fillings of the four live atlas relators.

The perfect-overlap scan proves that each of its certificate relators is
trivial in the universal central atlas cover.  Trivial classes are closed
under inversion, conjugacy, and multiplication.  This script therefore
starts with the cyclic conjugates of those certified relators and repeatedly
attaches another cyclic conjugate along the current boundary.  Free-product
reduction and all matrix arithmetic are exact over F_2.

This is a bounded disc-diagram search, not a proof that a survivor is
nontrivial when it is not found.  A positive result is a rigorous certificate
that the survivor belongs to the normal closure of the already killed
relators, and hence dies in R/[P,R].
"""

import argparse
import functools
import json
import sys

sys.path.insert(0, "experiments")

from atlas_kernel_collision_enumerator import (  # noqa: E402
    enumerate_ball,
    factor_projections,
    spanning_tree_kernel_words,
)
from atlas_two_chart_search import I4, matrix_key  # noqa: E402


IDENTITY = 0b1000010000100001


def matrix_to_bits(matrix):
    value = 0
    for row in range(4):
        for column in range(4):
            value |= int(matrix[row, column]) << (4 * row + column)
    return value


def multiply(left, right):
    value = 0
    for row in range(4):
        left_row = (left >> (4 * row)) & 0xF
        for column in range(4):
            parity = 0
            for middle in range(4):
                parity ^= ((left_row >> middle) & 1) * (
                    (right >> (4 * middle + column)) & 1)
            value |= parity << (4 * row + column)
    return value


@functools.cache
def inverse(matrix):
    augmented = [
        ((matrix >> (4 * row)) & 0xF) | (1 << (4 + row))
        for row in range(4)
    ]
    for column in range(4):
        pivot = next(row for row in range(column, 4)
                     if (augmented[row] >> column) & 1)
        augmented[column], augmented[pivot] = (
            augmented[pivot], augmented[column])
        for row in range(4):
            if row != column and ((augmented[row] >> column) & 1):
                augmented[row] ^= augmented[column]
    return sum(((augmented[row] >> 4) & 0xF) << (4 * row)
               for row in range(4))


def encode_word(word):
    return tuple((factor, matrix_to_bits(matrix)) for factor, matrix in word)


def free_reduce(word):
    stack = []
    for factor, matrix in word:
        if matrix == IDENTITY:
            continue
        if stack and stack[-1][0] == factor:
            product = multiply(stack[-1][1], matrix)
            stack.pop()
            if product != IDENTITY:
                stack.append((factor, product))
        else:
            stack.append((factor, matrix))
    return tuple(stack)


def invert_word(word):
    return tuple((factor, inverse(matrix))
                 for factor, matrix in reversed(word))


def cyclic_reduce(word):
    word = free_reduce(word)
    while len(word) > 1 and word[0][0] == word[-1][0]:
        factor = word[0][0]
        product = multiply(word[-1][1], word[0][1])
        word = word[1:-1]
        if product != IDENTITY:
            word += ((factor, product),)
        word = free_reduce(word)
    return word


def oriented_variants(word):
    core = cyclic_reduce(word)
    answer = {}
    for inverted, oriented in ((False, core), (True, invert_word(core))):
        for rotation in range(len(oriented)):
            value = oriented[rotation:] + oriented[:rotation]
            answer.setdefault(value, {
                "inverted": inverted,
                "rotation": rotation,
            })
    return answer


def canonical(word):
    variants = oriented_variants(word)
    return min(variants) if variants else ()


def seam_reduction(left, right):
    """Upper-bound the reduction available at one circular seam."""
    cancellations = 0
    limit = min(len(left), len(right))
    while (cancellations < limit
           and left[-1 - cancellations][0] == right[cancellations][0]
           and inverse(left[-1 - cancellations][1])
           == right[cancellations][1]):
        cancellations += 1
    reduction = 2 * cancellations
    if (cancellations < limit
            and left[-1 - cancellations][0] == right[cancellations][0]):
        reduction += 1
    return reduction


def attached_classes(state, attachment_variants, max_boundary):
    """Yield bounded cyclic classes obtained by attaching one killed cell."""
    for state_variant, state_operation in oriented_variants(state).items():
        for relator, index, relator_operation in attachment_variants:
            excess = len(state_variant) + len(relator) - max_boundary
            available = (seam_reduction(state_variant, relator)
                         + seam_reduction(relator, state_variant))
            if available < excess:
                continue
            product = cyclic_reduce(state_variant + relator)
            if not product or len(product) > max_boundary:
                continue
            yield canonical(product), {
                "parent_operation": state_operation,
                "certificate_word_index": index,
                "certificate_operation": relator_operation,
            }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", help="JSON from atlas_perfect_overlap_scan.py")
    parser.add_argument("--max-boundary", type=int, default=8)
    parser.add_argument("--max-cells", type=int, default=8)
    parser.add_argument("--max-states", type=int, default=200_000)
    parser.add_argument("--reverse-steps", type=int, default=0)
    parser.add_argument("--max-reverse-states", type=int, default=20_000)
    parser.add_argument("--progress", action="store_true")
    parser.add_argument("--output")
    args = parser.parse_args()

    with open(args.input, "r", encoding="utf-8") as stream:
        data = json.load(stream)
    states, _ = enumerate_ball(data["radius"])
    words, _, _ = spanning_tree_kernel_words(states)
    identity_key = matrix_key(I4)
    boundary = [word for word in words if any(
        matrix_key(projection) != identity_key
        for projection in factor_projections(word))]

    relators = {}
    for record in data["certificate_records"]:
        index = record["word_index"]
        word = encode_word(boundary[index])
        relators.setdefault(canonical(word), index)

    attachment_variants = []
    for word, index in relators.items():
        for variant, operation in oriented_variants(word).items():
            attachment_variants.append((variant, index, operation))

    target_indices = (11, 30, 44, 55)
    targets = {
        canonical(encode_word(boundary[index])): index
        for index in target_indices
    }
    found = {}
    known = {
        word: {
            "cells": 1,
            "certificate_word_index": index,
        }
        for word, index in relators.items()
        if len(word) <= args.max_boundary
    }
    frontier = list(known)
    layers = [{"cells": 1, "new_classes": len(frontier)}]
    state_cap_reached = False
    reverse_neighbor_checks = []
    reverse_certificates = {}

    def check_target_neighbors():
        newly_found = {}
        for target, index in targets.items():
            if index in found:
                continue
            for neighbor, operation in attached_classes(
                    target, attachment_variants, args.max_boundary):
                if neighbor in known:
                    cells = known[neighbor]["cells"] + 1
                    found[index] = cells
                    newly_found[index] = {
                        "cells": cells,
                        "meeting_class": neighbor,
                        **operation,
                    }
                    reverse_certificates[str(index)] = newly_found[index]
                    break
        reverse_neighbor_checks.append({
            "known_classes": len(known),
            "newly_found": sorted(newly_found),
        })

    check_target_neighbors()

    for cells in range(2, args.max_cells + 1):
        following = {}
        for state in frontier:
            for key, operation in attached_classes(
                    state, attachment_variants, args.max_boundary):
                if key in known or key in following:
                    continue
                following[key] = {
                    "cells": cells,
                    "parent": state,
                    **operation,
                }
                if key in targets:
                    found[targets[key]] = cells
                if len(known) + len(following) >= args.max_states:
                    state_cap_reached = True
                    break
            if state_cap_reached:
                break
        known.update(following)
        frontier = list(following)
        layers.append({"cells": cells, "new_classes": len(frontier)})
        check_target_neighbors()
        if args.progress:
            print(json.dumps({
                "cells": cells,
                "new_classes": len(frontier),
                "classes_reached": len(known),
                "survivors_found": found,
            }), file=sys.stderr, flush=True)
        if not frontier or state_cap_reached or len(found) == 4:
            break

    reverse_layers = []
    reverse_seen = {(target, index): 0 for target, index in targets.items()}
    reverse_frontier = list(reverse_seen)
    reverse_cap_reached = False
    for step in range(1, args.reverse_steps + 1):
        following = {}
        for state, target_index in reverse_frontier:
            for key, operation in attached_classes(
                    state, attachment_variants, args.max_boundary):
                tagged = (key, target_index)
                if tagged in reverse_seen or tagged in following:
                    continue
                following[tagged] = operation
                if key in known:
                    cells = known[key]["cells"] + step
                    found[target_index] = min(
                        found.get(target_index, cells), cells)
                if len(reverse_seen) + len(following) >= args.max_reverse_states:
                    reverse_cap_reached = True
                    break
            if reverse_cap_reached:
                break
        reverse_seen.update({tagged: step for tagged in following})
        reverse_frontier = list(following)
        reverse_layers.append({
            "steps": step,
            "new_classes": len(reverse_frontier),
            "classes_reached": len(reverse_seen),
        })
        if args.progress:
            print(json.dumps({
                "reverse_steps": step,
                "new_classes": len(reverse_frontier),
                "classes_reached": len(reverse_seen),
                "survivors_found": found,
            }), file=sys.stderr, flush=True)
        if not reverse_frontier or reverse_cap_reached:
            break

    result = {
        "certified_boundary_relators": data["perfect_overlap_certificates"],
        "certified_conjugacy_or_inverse_classes": len(relators),
        "attachment_variants": len(attachment_variants),
        "max_boundary": args.max_boundary,
        "max_cells_requested": args.max_cells,
        "max_states": args.max_states,
        "layers": layers,
        "reverse_neighbor_checks": reverse_neighbor_checks,
        "reverse_certificates": reverse_certificates,
        "reverse_layers": reverse_layers,
        "reverse_search_truncated_by_state_cap": reverse_cap_reached,
        "classes_reached": len(known),
        "search_truncated_by_state_cap": state_cap_reached,
        "survivor_cells_found": {
            str(index): found.get(index) for index in target_indices
        },
    }
    rendered = json.dumps(result, indent=2)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as stream:
            stream.write(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()
