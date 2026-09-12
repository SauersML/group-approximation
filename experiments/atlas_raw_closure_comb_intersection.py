"""Intersect the full order-512 raw Pauli closure with its comb conjugate.

This is a bounded exact-prefix audit.  Canonical common-depth keys avoid the
quadratic equality scan which would otherwise dominate the calculation.
"""

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
from atlas_raw_branch_pauli_cell import element_order, root  # noqa: E402
from atlas_raw_compressor_proper_infinite import (  # noqa: E402
    product,
    raw_and_comb,
    s,
    t,
)
from atlas_survivor_prefix_obstruction import leavitt_star  # noqa: E402


def main():
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
    transported = [
        product(leavitt_star(comb), value, comb) for value in closure
    ]
    states = [((), value) for value in (*closure, *transported)]
    depths = common_right_depths(states)
    closure_keys = {
        exact_image_key(value, depths): (value, word)
        for value, word in closure_with_words
    }
    transported_keys = {
        exact_image_key(value, depths): index
        for index, value in enumerate(transported)
    }
    intersection_keys = sorted(set(closure_keys) & set(transported_keys))
    entries = []
    for key in intersection_keys:
        value, word = closure_keys[key]
        entries.append({
            "order": element_order(value, 512),
            "word_in_X0_X1_Z0_Z1_raw": list(word),
            "comb_preimage_index": transported_keys[key],
        })
    result = {
        "raw_closure_order": len(closure),
        "comb_conjugate_order": len(transported),
        "intersection_order": len(intersection_keys),
        "intersection_entries": entries,
    }
    expected_path = Path(__file__).with_name(
        "atlas-raw-closure-comb-intersection.json")
    with expected_path.open(encoding="utf-8") as stream:
        expected = json.load(stream)
    if result != expected:
        raise AssertionError(result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
