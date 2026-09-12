"""Find the shortest relations mixing the raw order-512 packet and its comb copy.

Words are enumerated in the abstract free product ``K * K`` where
``K=<X0,X1,Z0,Z1,raw>``.  Adjacent syllables in the same factor are reduced
exactly inside ``K``.  Their images in the binary Leavitt-prefix group use the
second embedding ``k -> comb* k comb``.  A collision of two free-product
normal forms is therefore a genuine mixed kernel relation, not an internal
relation of either finite packet.
"""

import argparse
import collections
import json
import sys
from pathlib import Path

sys.path.insert(0, "experiments")

from atlas_kernel_collision_enumerator import (  # noqa: E402
    common_right_depths,
    exact_image_key,
)
from atlas_pauli_transported_carrier import (  # noqa: E402
    generated_subgroup_with_words,
)
from atlas_raw_branch_pauli_cell import root  # noqa: E402
from atlas_raw_compressor_proper_infinite import (  # noqa: E402
    product,
    raw_and_comb,
    s,
    t,
)
from atlas_survivor_prefix_obstruction import leavitt_star  # noqa: E402


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=int, default=3)
    args = parser.parse_args()
    if args.radius < 0:
        raise ValueError("radius must be nonnegative")

    raw, comb = raw_and_comb()
    generators = (
        root(t(0), 0, 1),
        root(t(1), 0, 1),
        root(s(0), 1, 2),
        root(s(1), 1, 2),
        raw,
    )
    closure_with_words = generated_subgroup_with_words(generators, limit=600)
    closure = [value for value, _word in closure_with_words]
    closure_depths = common_right_depths([((), value) for value in closure])
    closure_index = {
        exact_image_key(value, closure_depths): index
        for index, value in enumerate(closure)
    }
    closure_index_cache = {
        tuple(sorted(closure_depths.items())): closure_index
    }

    def index_in_closure(value):
        depths = dict(closure_depths)
        for left, right in value:
            degree = len(left) - len(right)
            depths[degree] = max(depths.get(degree, 0), len(right))
        depth_key = tuple(sorted(depths.items()))
        if depth_key not in closure_index_cache:
            closure_index_cache[depth_key] = {
                exact_image_key(candidate, depths): index
                for index, candidate in enumerate(closure)
            }
        return closure_index_cache[depth_key].get(exact_image_key(value, depths))

    def multiply_indices(left, right):
        value = product(closure[left], closure[right])
        return closure_index[exact_image_key(value, closure_depths)]

    generator_indices = [
        closure_index[exact_image_key(value, closure_depths)]
        for value in generators
    ]
    embedded = (
        closure,
        [product(leavitt_star(comb), value, comb) for value in closure],
    )
    normalizer_table = {}
    transported_generator_values = [embedded[1][index]
                                    for index in generator_indices]
    for transported_position, transported_generator in enumerate(
            transported_generator_values):
        row = {}
        for raw_position, raw_generator in enumerate(generators):
            conjugate = product(
                transported_generator, raw_generator, transported_generator)
            row[str(raw_position)] = index_in_closure(conjugate)
        normalizer_table[str(transported_position)] = row

    def append_syllable(normal_form, factor, index):
        if index == 0:
            return normal_form
        if normal_form and normal_form[-1][0] == factor:
            combined = multiply_indices(normal_form[-1][1], index)
            prefix = normal_form[:-1]
            return prefix if combined == 0 else prefix + ((factor, combined),)
        return normal_form + ((factor, index),)

    identity = product()
    states = {(): identity}
    frontier = [()]
    levels = [1]
    for _ in range(args.radius):
        following = []
        for normal_form in frontier:
            image = states[normal_form]
            for factor in (0, 1):
                for generator_index in generator_indices:
                    target = append_syllable(normal_form, factor, generator_index)
                    if target in states:
                        continue
                    states[target] = product(image, embedded[factor][generator_index])
                    following.append(target)
        frontier = following
        levels.append(len(frontier))

    state_items = list(states.items())
    image_depths = common_right_depths([
        (normal_form, value) for normal_form, value in state_items
    ])
    buckets = collections.defaultdict(list)
    for normal_form, value in state_items:
        buckets[exact_image_key(value, image_depths)].append(normal_form)
    collisions = [forms for forms in buckets.values() if len(forms) > 1]
    records = []
    for forms in collisions:
        forms = sorted(forms, key=lambda form: (len(form), form))
        records.append({
            "normal_forms": [
                [[factor, index] for factor, index in form]
                for form in forms[:4]
            ],
            "syllable_lengths": [len(form) for form in forms[:4]],
        })
    records.sort(key=lambda record: (
        max(record["syllable_lengths"]), record["normal_forms"]))

    shortest_collision_length = min(
        max(record["syllable_lengths"]) for record in records)
    result = {
        "radius": args.radius,
        "raw_closure_order": len(closure),
        "finite_generator_indices": generator_indices,
        "comb_generators_normalize_raw_closure": all(
            index is not None
            for row in normalizer_table.values() for index in row.values()),
        "comb_generator_action_on_raw_generators": normalizer_table,
        "free_product_ball_size": len(states),
        "level_sizes": levels,
        "mixed_collision_buckets": len(collisions),
        "shortest_collision_length": shortest_collision_length,
        "shortest_collision_buckets": sum(
            max(record["syllable_lengths"]) == shortest_collision_length
            for record in records),
    }
    if args.radius == 3:
        expected_path = Path(__file__).with_name(
            "atlas-raw-comb-mixed-relations.json")
        with expected_path.open(encoding="utf-8") as stream:
            expected = json.load(stream)
        if result != expected:
            raise AssertionError(result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
