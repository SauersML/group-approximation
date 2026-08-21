"""Exact overlap and two-projection holonomy of transported coefficient corners."""

from fractions import Fraction
import json
from pathlib import Path
import sys

sys.path.insert(0, "experiments")

from atlas_double_pauli_comb_blocks import (  # noqa: E402
    conjugate,
    cut,
    ga_add,
    ga_equal,
    ga_mul,
    ga_scale,
    ga_single,
    ga_sub,
    ga_trace,
    rational_string,
)
from atlas_raw_branch_pauli_cell import root  # noqa: E402
from atlas_raw_compressor_proper_infinite import (  # noqa: E402
    product,
    raw_and_comb,
)
from atlas_survivor_prefix_obstruction import (  # noqa: E402
    cylinder_projection,
)
from atlas_transported_coefficient_raw_character_mixing import (  # noqa: E402
    build_packet,
)


def main():
    comb, coefficient_involutions, cuts = build_packet()
    identity = ga_single(product())
    q = ga_add(*cuts.values())
    transported = tuple(
        conjugate(comb, involution) for involution in coefficient_involutions
    )
    corners = tuple(ga_mul(value, q, value) for value in transported)
    common = ga_mul(corners[0], corners[1])
    comb_cuts = {
        character: conjugate(comb, value)
        for character, value in cuts.items()
    }
    comb_corner = ga_add(*comb_cuts.values())

    raw, _ = raw_and_comb()
    z001 = ga_single(root(cylinder_projection("001")))
    c11 = ga_single(product(
        raw,
        root(cylinder_projection("11")),
        raw,
        root(cylinder_projection("11")),
    ))
    pauli_carrier = ga_mul(
        cut(identity, c11, negative=True),
        cut(identity, z001, negative=True),
    )
    transported_pauli_carrier = conjugate(comb, pauli_carrier)
    reflections = tuple(
        ga_sub(ga_scale(2, corner), identity) for corner in corners
    )

    overlap = ga_trace(ga_mul(corners[0], corners[1]))
    overlap_square = ga_trace(
        ga_mul(corners[0], corners[1], corners[0], corners[1])
    )
    angle_variance = overlap - overlap_square
    group_commutator = ga_mul(
        reflections[0], reflections[1], reflections[0], reflections[1]
    )
    commutator_hs_sq = 2 - 2 * ga_trace(group_commutator)

    result = {
        "corner_trace": rational_string(ga_trace(q)),
        "transported_corner_overlap": rational_string(overlap),
        "transported_corner_overlap_square": rational_string(overlap_square),
        "angle_variance": rational_string(angle_variance),
        "reflection_group_commutator_hs_sq": rational_string(
            commutator_hs_sq
        ),
        "commutator_equals_16_angle_variance": (
            commutator_hs_sq == 16 * angle_variance
        ),
        "transported_corners_commute": ga_equal(
            ga_mul(corners[0], corners[1]),
            ga_mul(corners[1], corners[0]),
        ),
        "common_product_is_projection": ga_equal(
            ga_mul(common, common), common
        ),
        "common_trace": rational_string(ga_trace(common)),
        "common_lies_under_raw_corner": ga_equal(ga_mul(q, common), common),
        "common_lies_under_comb_corner": ga_equal(
            ga_mul(comb_corner, common), common
        ),
        "common_equals_transported_pauli_carrier": ga_equal(
            common, transported_pauli_carrier
        ),
        "common_transported_pauli_carrier_overlap": rational_string(
            ga_trace(ga_mul(common, transported_pauli_carrier))
        ),
        "common_raw_cut_overlaps": {
            str(character): rational_string(ga_trace(ga_mul(common, cut)))
            for character, cut in cuts.items()
        },
        "common_comb_cut_overlaps": {
            str(character): rational_string(ga_trace(ga_mul(common, value)))
            for character, value in comb_cuts.items()
        },
        "common_commutes_raw_cuts": {
            str(character): ga_equal(
                ga_mul(common, value), ga_mul(value, common)
            )
            for character, value in cuts.items()
        },
        "common_commutes_comb_cuts": {
            str(character): ga_equal(
                ga_mul(common, value), ga_mul(value, common)
            )
            for character, value in comb_cuts.items()
        },
    }
    expected_path = Path(__file__).with_name(
        "atlas-transported-corner-overlap.json"
    )
    with expected_path.open(encoding="utf-8") as stream:
        expected = json.load(stream)
    if result != expected:
        raise AssertionError(result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
