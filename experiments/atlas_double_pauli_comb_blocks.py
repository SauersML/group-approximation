"""Audit exact comb blocks of the raw-invariant double-Pauli coefficient.

The underlying group elements are exact binary Leavitt-prefix matrices.  A
small rational group-algebra layer constructs the central cuts and the
two-sheet splices.  The calculation is deliberately symbolic and bounded:
it asks which coefficient-character blocks of comb transport vanish exactly,
not for a numerical representation or a large subgroup closure.
"""

from fractions import Fraction
import json
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, "experiments")

from atlas_raw_branch_pauli_cell import (  # noqa: E402
    element_order,
    generated_subgroup,
    inverse,
    root,
)
from atlas_raw_compressor_proper_infinite import (  # noqa: E402
    product,
    raw_and_comb,
    s,
    t,
)
from atlas_survivor_prefix_obstruction import (  # noqa: E402
    cylinder_projection,
    expand_terms,
    leavitt_star,
)


def ga_reduce(terms):
    """Combine equal exact group elements in a rational group-algebra sum."""
    entries = [
        (Fraction(coefficient), value)
        for coefficient, value in terms if coefficient
    ]
    depths = {}
    for _, value in entries:
        for left, right in value:
            degree = len(left) - len(right)
            depths[degree] = max(depths.get(degree, 0), len(right))
    buckets = {}
    representatives = {}
    order = []
    for coefficient, value in entries:
        key = tuple(sorted(expand_terms(value, depths)))
        if key not in buckets:
            buckets[key] = Fraction(0)
            representatives[key] = value
            order.append(key)
        buckets[key] += coefficient
    return [
        (buckets[key], representatives[key])
        for key in order if buckets[key]
    ]


def ga_single(value, coefficient=1):
    return ga_reduce([(Fraction(coefficient), value)])


def ga_add(*values):
    return ga_reduce([term for value in values for term in value])


def ga_scale(coefficient, value):
    return ga_reduce([
        (Fraction(coefficient) * old_coefficient, group_value)
        for old_coefficient, group_value in value
    ])


def ga_mul(*values):
    result = ga_single(product())
    for value in values:
        result = ga_reduce([
            (left_coefficient * right_coefficient,
             product(left_value, right_value))
            for left_coefficient, left_value in result
            for right_coefficient, right_value in value
        ])
    return result


def ga_sub(left, right):
    return ga_add(left, ga_scale(-1, right))


def ga_equal(left, right):
    return not ga_sub(left, right)


def ga_commute(left, right):
    return ga_equal(ga_mul(left, right), ga_mul(right, left))


def ga_trace(value):
    """Canonical group trace: coefficient of the identity group element."""
    identity = ga_single(product())
    return sum(
        coefficient for coefficient, group_value in value
        if ga_equal(ga_single(group_value), identity)
    )


def rational_string(value):
    return str(value.numerator) if value.denominator == 1 else str(value)


def cut(carrier, sign, negative=True):
    """The negative or positive cut of an involution in ``carrier``."""
    coefficient = -1 if negative else 1
    return ga_scale(Fraction(1, 2), ga_add(
        carrier, ga_scale(coefficient, ga_mul(carrier, sign))))


def conjugate(conjugator, value):
    unitary = ga_single(conjugator)
    inverse_unitary = ga_single(leavitt_star(conjugator))
    return ga_mul(inverse_unitary, value, unitary)


def main():
    raw, comb = raw_and_comb()
    identity = ga_single(product())
    raw_ga = ga_single(raw)

    x = (
        root(t(0), 0, 1),
        root(t(1), 0, 1),
    )
    z = (
        root(s(0), 1, 2),
        root(s(1), 1, 2),
    )
    c_raw = tuple(product(raw, value, raw, value) for value in x)
    a = tuple(product(x[index], c_raw[index]) for index in range(2))
    c = product(x[0], z[0], x[0], z[0])
    d = product(c_raw[0], z[0], c_raw[0], z[0])

    c_ga = ga_single(c)
    d_ga = ga_single(d)
    q = cut(identity, d_ga, negative=True)
    p = cut(identity, c_ga, negative=True)
    b = tuple(ga_add(
        ga_mul(p, ga_single(a[index])),
        ga_mul(ga_sub(identity, p), ga_single(x[index])),
    ) for index in range(2))
    bq = tuple(ga_mul(q, value) for value in b)

    coefficient_cuts = {}
    for epsilon0 in (-1, 1):
        for epsilon1 in (-1, 1):
            f0 = cut(q, b[0], negative=epsilon0 == -1)
            f1 = cut(q, b[1], negative=epsilon1 == -1)
            coefficient_cuts[(epsilon0, epsilon1)] = ga_mul(f0, f1)

    z11 = ga_single(root(cylinder_projection("11")))
    z001 = ga_single(root(cylinder_projection("001")))
    c11 = ga_single(product(
        raw,
        root(cylinder_projection("11")),
        raw,
        root(cylinder_projection("11")),
    ))
    carrier = ga_mul(
        cut(identity, c11, negative=True),
        cut(identity, z001, negative=True),
    )
    initial = ga_mul(cut(identity, z11, negative=True), carrier)
    transported_carrier = conjugate(comb, carrier)
    initial_complement = ga_sub(identity, initial)

    transported_coefficient_cuts = {
        key: conjugate(comb, value)
        for key, value in coefficient_cuts.items()
    }
    raw_group_generators = (*x, *z, raw)
    comb_group_generators = [
        product(leavitt_star(comb), value, comb)
        for value in raw_group_generators
    ]
    comb_generator_action_on_raw_coefficient_cuts = {}
    comb_generator_raw_commutators = []
    for generator_position, generator in enumerate(comb_group_generators):
        generator_ga = ga_single(generator)
        row = {}
        for source, source_cut in coefficient_cuts.items():
            moved = ga_mul(generator_ga, source_cut, generator_ga)
            row[str(source)] = next((
                str(target) for target, target_cut in coefficient_cuts.items()
                if ga_equal(moved, target_cut)
            ), None)
        comb_generator_action_on_raw_coefficient_cuts[
            str(generator_position)] = row
        raw_commutator = product(generator, raw, generator, raw)
        raw_commutator_inverse = product(raw, generator, raw, generator)
        commutator_action = {}
        for source, source_cut in coefficient_cuts.items():
            moved = ga_mul(
                ga_single(raw_commutator),
                source_cut,
                ga_single(raw_commutator_inverse),
            )
            commutator_action[str(source)] = next((
                str(target) for target, target_cut in coefficient_cuts.items()
                if ga_equal(moved, target_cut)
            ), None)
        comb_generator_raw_commutators.append({
            "generator_position": generator_position,
            "order_within_128": element_order(raw_commutator, 128),
            "raw_coefficient_cut_action": commutator_action,
        })
    pauli_packet = generated_subgroup((*x, *z), limit=64)
    transported_pauli_packet = [
        product(leavitt_star(comb), value, comb) for value in pauli_packet
    ]
    transported_pauli_normalizer_actions = []
    transported_pauli_cut_orbit = []
    orbit_source_cut = next(iter(coefficient_cuts.values()))
    for packet_index, packet_element in enumerate(transported_pauli_packet):
        packet_ga = ga_single(packet_element)
        packet_inverse_ga = ga_single(inverse(packet_element))
        moved_orbit_cut = ga_mul(
            packet_ga, orbit_source_cut, packet_inverse_ga)
        if not any(ga_equal(moved_orbit_cut, old)
                   for old in transported_pauli_cut_orbit):
            transported_pauli_cut_orbit.append(moved_orbit_cut)
        action = []
        for source_cut in coefficient_cuts.values():
            moved = ga_mul(packet_ga, source_cut, packet_inverse_ga)
            target = next((
                str(key) for key, target_cut in coefficient_cuts.items()
                if ga_equal(moved, target_cut)
            ), None)
            action.append(target)
        if all(target is not None for target in action):
            transported_pauli_normalizer_actions.append({
                "packet_index": packet_index,
                "action": action,
            })
    transported_pauli_cut_orbit_sum = ga_add(*transported_pauli_cut_orbit)
    orbit_base_overlap_traces = [
        ga_trace(ga_mul(orbit_source_cut, value))
        for value in transported_pauli_cut_orbit
    ]
    # The packet acts transitively on the orbit.  Hence every row of the Gram
    # matrix is a permutation of the base row; do not expand all 256 products.
    transported_pauli_cut_orbit_pair_trace_histogram = Counter(
        rational_string(value) for value in orbit_base_overlap_traces
    )
    transported_pauli_cut_orbit_pair_trace_histogram = Counter({
        key: 16 * multiplicity
        for key, multiplicity
        in transported_pauli_cut_orbit_pair_trace_histogram.items()
    })
    orbit_sum_raw_cut_overlaps = {
        key: sum(
            ga_trace(ga_mul(orbit_cut, raw_cut))
            for orbit_cut in transported_pauli_cut_orbit
        )
        for key, raw_cut in coefficient_cuts.items()
    }
    orbit_sum_trace_sq = 16 * sum(orbit_base_overlap_traces)
    orbit_sum_raw_coefficient_residual_hs_sq = (
        orbit_sum_trace_sq
        - 8 * sum(value * value
                  for value in orbit_sum_raw_cut_overlaps.values())
    )
    block_zero_table = {}
    block_trace_table = {}
    block_scaled_isometry_table = {}
    for source, source_cut in coefficient_cuts.items():
        block_zero_table[str(source)] = {}
        block_trace_table[str(source)] = {}
        block_scaled_isometry_table[str(source)] = {}
        for target, target_cut in transported_coefficient_cuts.items():
            block = ga_mul(source_cut, target_cut)
            block_zero_table[str(source)][str(target)] = not block
            block_trace_table[str(source)][str(target)] = rational_string(
                ga_trace(block))
            if source == (-1, -1) and target == (-1, -1):
                block_scaled_isometry_table[str(source)][str(target)] = {
                    "F_G_F_is_one_eighth_F": ga_equal(
                        ga_mul(source_cut, target_cut, source_cut),
                        ga_scale(Fraction(1, 8), source_cut)),
                    "G_F_G_is_one_eighth_G": ga_equal(
                        ga_mul(target_cut, source_cut, target_cut),
                        ga_scale(Fraction(1, 8), target_cut)),
                }

    result = {
        "two_sheet": {
            "q_terms": len(q),
            "B_terms": [len(value) for value in b],
            "B_corner_terms": [len(value) for value in bq],
            "B_corner_sq_is_q": [
                ga_equal(ga_mul(value, value), q) for value in bq
            ],
            "B_corner_raw_fixed": [
                ga_equal(ga_mul(raw_ga, value, raw_ga), value)
                for value in bq
            ],
            "B_corner_pair_commutes": ga_commute(bq[0], bq[1]),
            "B_corner_commutes_Z": [
                [ga_commute(bq[i], ga_single(z[j])) for j in range(2)]
                for i in range(2)
            ],
        },
        "coefficient_character_cuts": {
            "count": len(coefficient_cuts),
            "term_counts": {
                str(key): len(value) for key, value in coefficient_cuts.items()
            },
            "traces": {
                str(key): rational_string(ga_trace(value))
                for key, value in coefficient_cuts.items()
            },
            "pairwise_orthogonal": all(
                left == right or not ga_mul(left_cut, right_cut)
                for left, left_cut in coefficient_cuts.items()
                for right, right_cut in coefficient_cuts.items()
            ),
            "sum_is_q": ga_equal(
                ga_add(*coefficient_cuts.values()), q),
        },
        "comb_character_block_zero_table": block_zero_table,
        "comb_character_block_trace_table": block_trace_table,
        "comb_character_scaled_isometry_table":
            block_scaled_isometry_table,
        "comb_generator_action_on_raw_coefficient_cuts":
            comb_generator_action_on_raw_coefficient_cuts,
        "comb_generator_raw_commutators":
            comb_generator_raw_commutators,
        "transported_pauli_packet_order": len(transported_pauli_packet),
        "transported_pauli_coefficient_normalizer_order":
            len(transported_pauli_normalizer_actions),
        "transported_pauli_coefficient_normalizer_actions":
            transported_pauli_normalizer_actions,
        "transported_pauli_cut_orbit_order":
            len(transported_pauli_cut_orbit),
        "transported_pauli_cut_orbit_base_overlap_traces": sorted(
            rational_string(value) for value in orbit_base_overlap_traces),
        "transported_pauli_cut_orbit_pair_trace_histogram": dict(sorted(
            transported_pauli_cut_orbit_pair_trace_histogram.items())),
        "transported_pauli_cut_orbit_sum_terms":
            len(transported_pauli_cut_orbit_sum),
        "transported_pauli_cut_orbit_sum_trace_moments": [
            rational_string(ga_trace(transported_pauli_cut_orbit_sum)),
            rational_string(orbit_sum_trace_sq),
        ],
        "transported_pauli_cut_orbit_sum_invariant_by_orbit_construction":
            True,
        "transported_pauli_cut_orbit_sum_commutes_raw_coefficient_cuts": {
            str(key): ga_commute(
                transported_pauli_cut_orbit_sum, raw_cut)
            for key, raw_cut in coefficient_cuts.items()
        },
        "transported_pauli_cut_orbit_sum_raw_cut_overlaps": {
            str(key): rational_string(value)
            for key, value in orbit_sum_raw_cut_overlaps.items()
        },
        "transported_pauli_cut_orbit_sum_raw_coefficient_residual_hs_sq":
            rational_string(orbit_sum_raw_coefficient_residual_hs_sq),
        "transported_pauli_cut_orbit_sum_is_two_identity": ga_equal(
            transported_pauli_cut_orbit_sum, ga_scale(2, identity)),
        "transported_pauli_cut_orbit_sum_is_four_q": ga_equal(
            transported_pauli_cut_orbit_sum, ga_scale(4, q)),
        "comb_carrier_overlap_trace": rational_string(ga_trace(ga_mul(
            q, conjugate(comb, q)))),
        "pauli_carrier": {
            "carrier_terms": len(carrier),
            "initial_terms": len(initial),
            "transported_carrier_terms": len(transported_carrier),
            "raw_coefficient_cuts_commute_initial": all(
                ga_commute(value, initial)
                for value in coefficient_cuts.values()
            ),
            "transported_coefficient_cuts_commute_transported_carrier": all(
                ga_commute(value, transported_carrier)
                for value in transported_coefficient_cuts.values()
            ),
            "full_containment_leakage_is_zero": not ga_mul(
                initial_complement, transported_carrier),
            "raw_character_sector_leakage_zero": {
                str(key): not ga_mul(
                    initial_complement, transported_carrier, value)
                for key, value in coefficient_cuts.items()
            },
        },
    }
    expected_path = Path(__file__).with_name(
        "atlas-double-pauli-comb-blocks.json")
    with expected_path.open(encoding="utf-8") as stream:
        expected = json.load(stream)
    if result != expected:
        raise AssertionError(result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
