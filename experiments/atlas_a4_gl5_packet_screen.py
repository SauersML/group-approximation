#!/usr/bin/env python3
"""Exhaust the GL5(F2) finite-quotient screen for the 30-word A4 packet.

Embed H=GL4(F2)=A8 as diag(GL4,1) in GL5(F2).  A relative chart position h
produces the second copy h H h^-1.  The quotient GL5/H has only 496 cosets:
a coset is exactly a pair (line l, complementary hyperplane ker(phi)) with
phi(l)=1.  For each coset h0 H we test all 20,160 internal alignments k in H,
but do so through precomputed conjugacy-class masks for the ten moving packet
letters.  This is an exact exhaustive classification of all 9,999,360 elements
of GL5(F2), not a random search.

Expected result:

* exactly 202 relative positions satisfy all thirty shortest A4 pair-cubes;
* they lie in exactly 25 of the 496 cosets;
* their intersections H cap hHh^-1 have sizes 20160, 1344 or 168, with
  30, 54 and 118 solutions respectively;
* collision 19243 is nonidentity for every one of the 202 solutions; its order
  is 2 in 157 cases and 4 in 45 cases.

All arithmetic is exact over F2.
"""

import argparse
import collections
import json
import os

import numpy as np

from atlas_a4_packet_generation import matrix_order, select_packet, x_lengths
from atlas_a4_rank_three_core import H18_LABEL_HEX, packet_edge
from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_packet import decode_word
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key
from atlas_t30_parabolic_c3_bridge import (
    H6_LABELS,
    H18_LABELS,
    I4 as I4_TUPLE,
    Q_FIRST_INVOLUTION,
    Q_SECOND,
    center,
    matrix_hex,
    subgroup,
)


I5 = np.eye(5, dtype=np.uint8)


def embed4(matrix):
    out = I5.copy()
    out[:4, :4] = matrix
    return out


def mul5(left, right):
    return (left @ right) & 1


def inv5(matrix):
    aug = np.concatenate((matrix.copy(), I5.copy()), axis=1)
    for col in range(5):
        pivot = next(row for row in range(col, 5) if aug[row, col])
        aug[[col, pivot]] = aug[[pivot, col]]
        for row in range(5):
            if row != col and aug[row, col]:
                aug[row] ^= aug[col]
    return aug[:, 5:]


def graph4(matrix):
    """The outer inverse-transpose automorphism of GL4(F2)."""
    return gf2_inv(matrix).T.copy()


def twist_second_word(word):
    return [
        (factor, graph4(matrix) if factor == 2 else matrix)
        for factor, matrix in word
    ]


def key5(matrix):
    return bytes(matrix.reshape(-1))


def rows5(matrix):
    return tuple(
        sum(int(matrix[row, col]) << col for col in range(5))
        for row in range(5)
    )


def row_mul(left, right):
    out = []
    for mask in left:
        value = 0
        bit = 0
        while mask:
            if mask & 1:
                value ^= right[bit]
            mask >>= 1
            bit += 1
        out.append(value)
    return tuple(out)


I5_ROWS = rows5(I5)


def cube_is_identity(matrix_rows):
    return row_mul(row_mul(matrix_rows, matrix_rows), matrix_rows) == I5_ROWS


def order5(matrix, bound=64):
    value = I5.copy()
    for exponent in range(1, bound + 1):
        value = mul5(value, matrix)
        if np.array_equal(value, I5):
            return exponent
    raise AssertionError("unexpected order above bound")


def nonzero_fixed_points(matrix):
    """Fixed points in the 31-point permutation action on nonzero F2^5."""
    return sum(
        np.array_equal((matrix @ bits5(value)) & 1, bits5(value))
        for value in range(1, 32)
    )


def covariance_defect_numerator(relative, label):
    """Return 31*delta^2 in the 31-point permutation representation.

    For the permutation representation, normalized trace is the fixed-point
    fraction.  Hence delta_U(g)^2=2(1-fix([U,g])/31), and the integer returned
    here is exactly 31 times that squared defect.
    """
    relative_inverse = inv5(relative)
    image = embed4(label)
    cocycle = mul5(
        mul5(mul5(relative, image), relative_inverse),
        inv5(image),
    )
    return 2 * (31 - nonzero_fixed_points(cocycle))


def rank_columns(vectors):
    if not vectors:
        return 0
    matrix = np.column_stack(vectors).copy()
    rank = 0
    for col in range(matrix.shape[1]):
        pivot = next(
            (row for row in range(rank, matrix.shape[0]) if matrix[row, col]),
            None,
        )
        if pivot is None:
            continue
        matrix[[rank, pivot]] = matrix[[pivot, rank]]
        for row in range(matrix.shape[0]):
            if row != rank and matrix[row, col]:
                matrix[row] ^= matrix[rank]
        rank += 1
    return rank


def bits5(number):
    return np.array([(number >> index) & 1 for index in range(5)], dtype=np.uint8)


def coset_representatives():
    """Represent GL5/H by (line, complementary hyperplane) pairs."""
    representatives = []
    for line_bits in range(1, 32):
        line = bits5(line_bits)
        for covector_bits in range(1, 32):
            covector = bits5(covector_bits)
            if int(covector @ line) % 2 != 1:
                continue
            kernel_vectors = [
                bits5(value)
                for value in range(1, 32)
                if int(covector @ bits5(value)) % 2 == 0
            ]
            basis = []
            for vector in kernel_vectors:
                if rank_columns(basis + [vector]) > len(basis):
                    basis.append(vector)
                if len(basis) == 4:
                    break
            representative = np.column_stack(basis + [line]).astype(np.uint8)
            representatives.append((representative, inv5(representative)))
    if len(representatives) != 496:
        raise AssertionError("GL5/H coset count changed")
    return representatives


def collision_value(word, relative):
    inverse = inv5(relative)
    value = I5.copy()
    for factor, matrix in word:
        image = embed4(matrix)
        if factor == 2:
            image = mul5(mul5(relative, image), inverse)
        value = mul5(value, image)
    return value


def intersection_size(h, h_inverse, H, H_keys):
    count = 0
    for element in H:
        moved = mul5(mul5(h, element), h_inverse)
        if key5(moved) in H_keys:
            count += 1
    return count


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--core",
        action="store_true",
        help="retain only the fourteen rank-three packet relators",
    )
    parser.add_argument(
        "--first-collision-survivor",
        action="store_true",
        help="stop after the first exact packet position with q_19243=1",
    )
    parser.add_argument(
        "--central-mask",
        type=lambda value: int(value, 0),
        default=0,
        help="with --core, add the indicated subset of eight distinct central-C3 constraints",
    )
    parser.add_argument(
        "--list-central-constraints",
        action="store_true",
        help="print the canonical eight distinct central-C3 constraints and stop",
    )
    parser.add_argument(
        "--list-core-constraints",
        action="store_true",
        help="print the canonical eight distinct rank-three core constraints and stop",
    )
    parser.add_argument(
        "--central-singleton-survivors",
        action="store_true",
        help="find q=1 core positions surviving each one of the eight central constraints",
    )
    parser.add_argument(
        "--dual-second",
        action="store_true",
        help="apply inverse-transpose to every factor-two chart label",
    )
    args = parser.parse_args()

    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    full_packet = select_packet(words, x_lengths())
    if args.dual_second:
        full_packet = [
            (index, twist_second_word(word)) for index, word in full_packet
        ]
    packet = full_packet
    selected_central_constraints = 0
    ordered_central = []
    if args.core:
        h18_for_core = subgroup(tuple(
            tuple(tuple(int(bit) for bit in row) for row in np.frombuffer(
                bytes.fromhex(value), dtype=np.uint8
            ).reshape(4, 4))
            for value in H18_LABEL_HEX
        ))
        central_order_three = {
            bytes(np.asarray(value, dtype=np.uint8).reshape(-1))
            for value in center(h18_for_core)
            if value != I4_TUPLE
        }
        core_packet = [
            entry for entry in packet
            if matrix_key(packet_edge(entry[1])[2]) not in central_order_three
        ]
        central_packet = [
            entry for entry in packet
            if matrix_key(packet_edge(entry[1])[2]) in central_order_three
        ]
        if len(core_packet) != 14 or len(central_packet) != 16:
            raise AssertionError("the 14+16 packet decomposition changed")

        if args.list_core_constraints:
            core_relations = {}
            for entry in core_packet:
                by_factor = {factor: matrix for factor, matrix in entry[1]}
                key = (matrix_key(by_factor[1]), matrix_key(by_factor[2]))
                core_relations.setdefault(key, []).append(entry)
            print(json.dumps({
                "core_constraints": [
                    {
                        "first_hex": first.hex(),
                        "occurrences": len(entries),
                        "second_hex": second.hex(),
                        "tree_indices": [entry[0] for entry in entries],
                    }
                    for (first, second), entries in sorted(core_relations.items())
                ],
                "distinct_constraints": len(core_relations),
                "word_occurrences": len(core_packet),
            }, indent=2, sort_keys=True))
            return

        central_relations = {}
        for entry in central_packet:
            by_factor = {factor: matrix for factor, matrix in entry[1]}
            key = (matrix_key(by_factor[1]), matrix_key(by_factor[2]))
            central_relations.setdefault(key, []).append(entry)
        ordered_central = sorted(central_relations.items())
        if len(ordered_central) != 8:
            raise AssertionError("expected eight distinct central-C3 constraints")
        if args.central_mask < 0 or args.central_mask >= (1 << len(ordered_central)):
            raise ValueError("--central-mask must lie between 0 and 255")
        if args.list_central_constraints:
            print(json.dumps({
                "central_constraint_orbit": [
                    {
                        "bit": bit,
                        "first_hex": first.hex(),
                        "occurrences": len(entries),
                        "second_hex": second.hex(),
                        "tree_indices": [entry[0] for entry in entries],
                    }
                    for bit, ((first, second), entries) in enumerate(ordered_central)
                ],
                "distinct_constraints": len(ordered_central),
                "word_occurrences": len(central_packet),
            }, indent=2, sort_keys=True))
            return
        selected_entries = [
            entries[0]
            for bit, (_key, entries) in enumerate(ordered_central)
            if args.central_mask & (1 << bit)
        ]
        selected_central_constraints = len(selected_entries)
        packet = core_packet + selected_entries
    elif (
        args.central_mask
        or args.list_central_constraints
        or args.list_core_constraints
        or args.central_singleton_survivors
    ):
        raise ValueError("central-constraint options require --core")

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as handle:
        collision = decode_word(json.load(handle)[0]["word"])
    if args.dual_second:
        collision = twist_second_word(collision)

    GL4 = enumerate_gl4()
    GL4_index = {matrix_key(matrix): index for index, matrix in enumerate(GL4)}
    GL4_inverse = [gf2_inv(matrix) for matrix in GL4]
    H = [embed4(matrix) for matrix in GL4]
    H_rows = [rows5(matrix) for matrix in H]
    H_keys = {key5(matrix) for matrix in H}

    # The moving (factor-two) packet alphabet has ten elements: four
    # transvections and six order-three elements.  Precompute how every
    # internal alignment conjugates each of them inside H.
    relation_data = []
    moving_keys = set()
    for index, word in packet:
        by_factor = {}
        for factor, matrix in word:
            by_factor[factor] = matrix
        first, second = by_factor[1], by_factor[2]
        relation_data.append(
            (index, first, matrix_order(first), second, matrix_order(second))
        )
        moving_keys.add(matrix_key(second))

    moving = {
        key: np.frombuffer(key, dtype=np.uint8).reshape(4, 4).copy()
        for key in moving_keys
    }
    conjugate_index = {}
    for key, label in moving.items():
        values = np.empty(len(GL4), dtype=np.int32)
        for position, (alignment, inverse) in enumerate(zip(GL4, GL4_inverse)):
            moved = gf2_mul(gf2_mul(alignment, label), inverse)
            values[position] = GL4_index[matrix_key(moved)]
        conjugate_index[key] = values

    # All moving involutions are in one class (105 elements), and all moving
    # order-three labels are in one class (1120 elements).
    classes = {}
    for key, values in conjugate_index.items():
        order = matrix_order(moving[key])
        orbit = tuple(sorted(set(int(value) for value in values)))
        if order in classes and classes[order] != orbit:
            raise AssertionError("moving packet labels split into unexpected classes")
        classes[order] = orbit
    if {order: len(values) for order, values in classes.items()} != {2: 105, 3: 1120}:
        raise AssertionError("unexpected packet conjugacy-class sizes")

    # Duplicate occurrences of the same ordered pair impose the same condition.
    unique_relations = {}
    for index, first, first_order, second, second_order in relation_data:
        key = (matrix_key(first), matrix_key(second), first_order, second_order)
        unique_relations.setdefault(key, []).append(index)
    expected_distinct_relations = (
        8 + selected_central_constraints if args.core else 16
    )
    if len(unique_relations) != expected_distinct_relations:
        raise AssertionError(
            f"expected {expected_distinct_relations} distinct ordered pair constraints"
        )

    relation_specs = []
    for (first_key, second_key, first_order, second_order), indices in unique_relations.items():
        first = np.frombuffer(first_key, dtype=np.uint8).reshape(4, 4).copy()
        relation_specs.append(
            (second_order, rows5(embed4(first)), second_key, tuple(indices))
        )
    # Smaller order-two class first for faster exact pruning.
    relation_specs.sort(key=lambda item: (item[0] != 2, len(item[3])))

    solutions = []
    coset_solution_counts = collections.Counter()
    singleton_survivors = {}
    central_pattern_histogram = collections.Counter()
    for coset_index, (representative, representative_inverse) in enumerate(
        coset_representatives()
    ):
        rep_rows = rows5(representative)
        rep_inverse_rows = rows5(representative_inverse)
        class_images = {}
        for order in (2, 3):
            class_images[order] = {
                element_index: row_mul(
                    row_mul(rep_rows, H_rows[element_index]), rep_inverse_rows
                )
                for element_index in classes[order]
            }

        surviving = np.ones(len(GL4), dtype=bool)
        for moving_order, first_rows, moving_key, _indices in relation_specs:
            if not surviving.any():
                break
            allowed = np.zeros(len(GL4), dtype=bool)
            for element_index, image_rows in class_images[moving_order].items():
                # (xy)^3=1 iff (yx)^3=1, so the factor-reversed packet
                # orientation needs no separate test here.
                if cube_is_identity(row_mul(image_rows, first_rows)):
                    allowed[element_index] = True
            surviving &= allowed[conjugate_index[moving_key]]

        positions = np.flatnonzero(surviving)
        if len(positions):
            coset_solution_counts[len(positions)] += 1
        for position in positions:
            relative = mul5(representative, H[int(position)])
            if args.central_singleton_survivors:
                if not np.array_equal(collision_value(collision, relative), I5):
                    continue
                satisfied_mask = 0
                for bit, (_key, entries) in enumerate(ordered_central):
                    value = collision_value(entries[0][1], relative)
                    if np.array_equal(mul5(mul5(value, value), value), I5):
                        satisfied_mask |= 1 << bit
                        singleton_survivors.setdefault(bit, key5(relative).hex())
                central_pattern_histogram[satisfied_mask] += 1
                if len(singleton_survivors) == 8:
                    print(json.dumps({
                        "all_singletons_found": True,
                        "central_pattern_histogram_before_stop": {
                            hex(mask): count
                            for mask, count in sorted(central_pattern_histogram.items())
                        },
                        "singleton_survivors": {
                            str(bit): relative_hex
                            for bit, relative_hex in sorted(singleton_survivors.items())
                        },
                    }, indent=2, sort_keys=True))
                    return
                continue
            if args.first_collision_survivor and np.array_equal(
                collision_value(collision, relative), I5
            ):
                relative_inverse = inv5(relative)
                core_checks = [
                    np.array_equal(
                        mul5(
                            mul5(collision_value(word, relative), collision_value(word, relative)),
                            collision_value(word, relative),
                        ),
                        I5,
                    )
                    for _index, word in packet
                ]
                full_checks = [
                    np.array_equal(
                        mul5(
                            mul5(collision_value(word, relative), collision_value(word, relative)),
                            collision_value(word, relative),
                        ),
                        I5,
                    )
                    for _index, word in full_packet
                ]
                rank_three_labels = [
                    (f"H6[{label_index}]", np.asarray(label, dtype=np.uint8))
                    for label_index, label in enumerate(H6_LABELS)
                ] + [
                    (f"Q_SECOND[{label_index}]", np.asarray(label, dtype=np.uint8))
                    for label_index, label in enumerate(Q_SECOND)
                ]
                moved_rank_three = []
                for label_name, label in rank_three_labels:
                    image = embed4(label)
                    cocycle = mul5(
                        mul5(mul5(relative, image), relative_inverse),
                        inv5(image),
                    )
                    if not np.array_equal(cocycle, I5):
                        moved_rank_three.append({
                            "label": label_name,
                            "cocycle_hex": key5(cocycle).hex(),
                            "cocycle_order": order5(cocycle),
                        })
                print(json.dumps({
                    "core": args.core,
                    "collision_19243_identity_survivor": key5(relative).hex(),
                    "collision_19243_value_hex": key5(I5).hex(),
                    "coset_index": coset_index,
                    "chart_intersection_order": intersection_size(
                        relative, relative_inverse, H, H_keys
                    ),
                    "core_relations_satisfied": sum(core_checks),
                    "core_relations_total": len(core_checks),
                    "full_packet_relations_satisfied": sum(full_checks),
                    "full_packet_relations_total": len(full_checks),
                    "internal_alignment_index": int(position),
                    "moved_rank_three_generators": moved_rank_three,
                }, indent=2, sort_keys=True))
                return
            solutions.append((coset_index, int(position), relative))

    if args.central_singleton_survivors:
        print(json.dumps({
            "all_singletons_found": len(singleton_survivors) == 8,
            "central_pattern_histogram": {
                hex(mask): count
                for mask, count in sorted(central_pattern_histogram.items())
            },
            "singleton_survivors": {
                str(bit): relative_hex
                for bit, relative_hex in sorted(singleton_survivors.items())
            },
        }, indent=2, sort_keys=True))
        return

    if not args.core and len(solutions) != 202:
        raise AssertionError(f"expected 202 packet solutions, got {len(solutions)}")
    if len({key5(relative) for _, _, relative in solutions}) != len(solutions):
        raise AssertionError("duplicate packet solutions")

    intersection_histogram = collections.Counter()
    collision_order_histogram = collections.Counter()
    joint_histogram = collections.Counter()
    two_holonomy_histogram = collections.Counter()
    collision_defect_histogram = collections.Counter()
    joint_two_holonomy_collision_histogram = collections.Counter()
    joint_stratum_two_holonomy_collision_histogram = collections.Counter()
    collision_survivors = 0

    # The exact bridge uses c=h k and a=z b.  The frozen labels below are the
    # same canonical choices as experiments/atlas_t30_parabolic_c3_bridge.py.
    h = np.array(H6_LABELS[2], dtype=np.uint8)
    k = np.array(Q_SECOND[0], dtype=np.uint8)
    c = gf2_mul(h, k)
    h18 = subgroup(H18_LABELS)
    z_values = sorted(
        (value for value in center(h18) if value != I4_TUPLE),
        key=matrix_hex,
    )
    z = np.array(z_values[0], dtype=np.uint8)
    b = np.array(Q_FIRST_INVOLUTION, dtype=np.uint8)
    a = gf2_mul(z, b)
    for _coset, _position, relative in solutions:
        relative_inverse = inv5(relative)
        overlap = intersection_size(relative, relative_inverse, H, H_keys)
        q_value = collision_value(collision, relative)
        q_order = order5(q_value)
        c_defect_numerator = covariance_defect_numerator(relative, c)
        a_defect_numerator = covariance_defect_numerator(relative, a)
        # 31*E_2HOL = 2*(31*delta(c)^2) + 31*delta(a)^2.
        two_holonomy_numerator = 2 * c_defect_numerator + a_defect_numerator
        collision_defect_numerator = 2 * (31 - nonzero_fixed_points(q_value))
        intersection_histogram[overlap] += 1
        collision_order_histogram[q_order] += 1
        joint_histogram[(overlap, q_order)] += 1
        two_holonomy_histogram[two_holonomy_numerator] += 1
        collision_defect_histogram[collision_defect_numerator] += 1
        joint_two_holonomy_collision_histogram[
            (two_holonomy_numerator, collision_defect_numerator)
        ] += 1
        joint_stratum_two_holonomy_collision_histogram[
            (overlap, two_holonomy_numerator, collision_defect_numerator)
        ] += 1
        collision_survivors += int(np.array_equal(q_value, I5))

    expected_intersections = {168: 118, 1344: 54, 20160: 30}
    expected_collision_orders = {2: 157, 4: 45}
    expected_joint = {
        (168, 2): 88,
        (168, 4): 30,
        (1344, 2): 44,
        (1344, 4): 10,
        (20160, 2): 25,
        (20160, 4): 5,
    }
    expected_cosets = {3: 6, 4: 2, 5: 4, 7: 6, 8: 1, 14: 3, 17: 2, 30: 1}

    if not args.core:
        if dict(intersection_histogram) != expected_intersections:
            raise AssertionError(intersection_histogram)
        if dict(collision_order_histogram) != expected_collision_orders:
            raise AssertionError(collision_order_histogram)
        if dict(joint_histogram) != expected_joint:
            raise AssertionError(joint_histogram)
        if collision_survivors != 0:
            raise AssertionError("collision 19243 survived the GL5 screen")
        if dict(coset_solution_counts) != expected_cosets:
            raise AssertionError(coset_solution_counts)
        if any(
            energy > 5 * defect
            for energy, defect in joint_two_holonomy_collision_histogram
        ):
            raise AssertionError("the sharp rank-five E_2HOL <= 5 ||q-1||_2^2 wall failed")
    sharp_readout_count = sum(
        count
        for (energy, defect), count in joint_two_holonomy_collision_histogram.items()
        if energy == 5 * defect
    )
    if not args.core and sharp_readout_count != 96:
        raise AssertionError(f"sharp readout count changed: {sharp_readout_count}")

    output = {
        "ambient_group": "GL5(F2)",
        "ambient_order": 9999360,
        "chart_group": "GL4(F2)=A8",
        "chart_order": 20160,
        "factor_two_label_parity": "dual" if args.dual_second else "natural",
        "cosets_tested": 496,
        "packet_relations": len(packet),
        "distinct_ordered_pair_constraints": expected_distinct_relations,
        "packet_exact_relative_positions": len(solutions),
        "packet_exact_relative_positions_hex": (
            [] if args.core else [
                key5(relative).hex() for _, _, relative in solutions
            ]
        ),
        "packet_solution_cosets": sum(coset_solution_counts.values()),
        "solutions_per_nonempty_coset_histogram": dict(sorted(coset_solution_counts.items())),
        "chart_intersection_size_histogram": dict(sorted(intersection_histogram.items())),
        "collision_19243_identity_survivors": collision_survivors,
        "collision_19243_order_histogram": dict(sorted(collision_order_histogram.items())),
        "permutation31_two_holonomy_energy_numerator_over_31_histogram": dict(
            sorted(two_holonomy_histogram.items())
        ),
        "permutation31_collision_defect_squared_numerator_over_31_histogram": dict(
            sorted(collision_defect_histogram.items())
        ),
        "permutation31_joint_two_holonomy_collision_histogram": {
            f"E2_num={energy},q_defect2_num={defect}": count
            for (energy, defect), count
            in sorted(joint_two_holonomy_collision_histogram.items())
        },
        "permutation31_joint_stratum_two_holonomy_collision_histogram": {
            f"intersection={overlap},E2_num={energy},q_defect2_num={defect}": count
            for (overlap, energy, defect), count
            in sorted(joint_stratum_two_holonomy_collision_histogram.items())
        },
        "permutation31_sharp_readout": {
            "inequality": "E_2HOL <= 5 ||q_19243-1||_2^2",
            "equality_positions": sharp_readout_count,
        },
        "joint_intersection_collision_order_histogram": {
            f"intersection={overlap},q_order={order}": count
            for (overlap, order), count in sorted(joint_histogram.items())
        },
    }
    print(json.dumps(output, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
