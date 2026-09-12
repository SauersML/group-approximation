"""Lift compact projective harmonic cycles through the filtered HAP complex.

The compact cellular complex is the zero vertical row of HAP's Wall total
complex.  Its two degree-two cells are the last two free generators of total
degree two.  A signed-coinvariant cycle therefore has a canonical sparse
lift obtained by choosing one coefficient point in every orbit.  This script
cancels the resulting positive-filtration syndrome, first in bidegree
``(1,1)`` and then in ``(0,2)``, over a specified prime field.  It also
retains one deterministic solution of the first equation and measures the
resulting class in vertex-stabilizer homology before the homogeneous
horizontal correction is applied.

Run with Sage's Python.  The full boundary prefix is the prefix passed to
``sl3_projective_h2_export.g``; only ``-d2.tsv`` is needed here.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

from sage.all import GF, matrix, vector

from sl3_projective_cellular_analyze import (
    SignedDSU,
    build_boundaries,
    coinvariants,
    parse,
)
from sl3_projective_derived_e1 import coordinate_indices, read_boundary


def read_harmonic_basis(path: Path, dimension: int):
    rows = []
    with path.open(encoding="ascii") as stream:
        header = stream.readline().split()
        if not header or header[0] != "coordinate":
            raise ValueError("invalid harmonic basis header")
        rank = len(header) - 1
        rows = [[] for _ in range(rank)]
        for expected_coordinate, line in enumerate(stream):
            fields = line.split()
            if int(fields[0]) != expected_coordinate:
                raise ValueError("harmonic coordinates are not consecutive")
            if len(fields) != rank + 1:
                raise ValueError("invalid harmonic basis row")
            for basis_index, value in enumerate(fields[1:]):
                rows[basis_index].append(int(value))
    if any(len(row) != dimension for row in rows):
        raise ValueError("harmonic basis has the wrong ambient dimension")
    return rows


def compact_representatives(degree: int, cells):
    """Return one coefficient point for every compact degree-two coordinate."""

    representatives = []
    for cell_index in (1, 2):
        dimension, coordinate_map = coinvariants(degree, cells[(2, cell_index)])
        local_representatives = [None] * dimension
        for point, value in enumerate(coordinate_map):
            if value is None:
                continue
            coordinate, _sign = value
            if local_representatives[coordinate] is None:
                local_representatives[coordinate] = point
        if any(point is None for point in local_representatives):
            raise AssertionError("coinvariant coordinate has no representative")
        for coordinate, point in enumerate(local_representatives):
            _root_coordinate, source_sign = coordinate_map[point]
            if _root_coordinate != coordinate:
                raise AssertionError("invalid compact representative")
            representatives.append((cell_index, point, source_sign))
    return representatives


def signed_torsion_representatives(degree: int, cell):
    """Choose one point in every signed orbit killed by a minus stabilizer."""

    dsu = SignedDSU(degree)
    for sign, permutation in cell.stabilizers:
        for source, target in enumerate(permutation):
            dsu.union(source, target, sign)
    representatives = {}
    for point in range(degree):
        root, _sign = dsu.find(point)
        root, _ = dsu.find(root)
        if dsu.bad[root] and root not in representatives:
            representatives[root] = point
    return list(representatives.values())


def induced_compact_boundary(
    full_boundary, degree: int, cells, representatives, cell_generators
):
    """Augment the HAP zero row and recover its compact cellular boundary."""

    field = full_boundary.base_ring()
    target_dimension, target_map = coinvariants(degree, cells[(1, 1)])
    entries = {}
    for compact_source, (cell_index, point, source_sign) in enumerate(representatives):
        full_source = cell_generators[cell_index - 1] * degree + point
        for full_target, coefficient in full_boundary.row(full_source).dict().items():
            target_generator, target_point = divmod(full_target, degree)
            if target_generator != 3:
                continue
            target_value = target_map[target_point]
            if target_value is None:
                continue
            compact_target, target_sign = target_value
            value = field(source_sign * target_sign) * coefficient
            key = (compact_source, compact_target)
            entries[key] = entries.get(key, field.zero()) + value
    return matrix(
        field,
        len(representatives),
        target_dimension,
        {key: value for key, value in entries.items() if value},
        sparse=True,
    )


def solve_filtered_lift(
    boundary, degree: int, compact_lift, q2_torsion_source_indices
):
    field = boundary.base_ring()
    target_q1 = coordinate_indices(1, 1, degree)
    target_q0 = coordinate_indices(1, 0, degree)
    source_q1 = coordinate_indices(2, 1, degree)
    source_q0 = coordinate_indices(2, 0, degree)

    initial_boundary = compact_lift * boundary
    q1_syndrome = vector(field, [initial_boundary[index] for index in target_q1])
    q1_block = boundary.matrix_from_rows_and_columns(source_q1, target_q1)
    q1_rank = int(q1_block.rank())
    q1_augmented_rank = int(q1_block.stack(matrix(field, [q1_syndrome])).rank())
    # Keep the same source order used below: torsion first, then A_(1,1).
    q1_with_torsion = boundary.matrix_from_rows_and_columns(
        list(q2_torsion_source_indices) + source_q1, target_q1)
    try:
        q1_particular = q1_with_torsion.solve_left(-q1_syndrome)
    except ValueError:
        return {
            "q1_solvable_without_orientation_torsion": (
                q1_augmented_rank == q1_rank),
            "q1_solvable_with_orientation_torsion": False,
            "q1_block_rank": q1_rank,
            "q1_augmented_rank": q1_augmented_rank,
            "q1_syndrome_support": len(q1_syndrome.support()),
        }, None, None

    correction_indices = (
        list(q2_torsion_source_indices) + source_q1 + source_q0)
    correction_block = boundary.matrix_from_rows(correction_indices)
    try:
        correction = correction_block.solve_left(-initial_boundary)
    except ValueError:
        return {
            "q1_solvable_without_orientation_torsion": (
                q1_augmented_rank == q1_rank),
            "q1_solvable_with_orientation_torsion": True,
            "total_lift_solvable": False,
            "q1_block_rank": q1_rank,
            "q1_augmented_rank": q1_augmented_rank,
            "q1_syndrome_support": len(q1_syndrome.support()),
        }, None, None

    total_correction = vector(field, boundary.nrows())
    for local, total in enumerate(correction_indices):
        total_correction[total] = correction[local]
    total_lift = compact_lift + total_correction
    if total_lift * boundary:
        raise AssertionError("filtered correction is not a total cycle")

    torsion_count = len(q2_torsion_source_indices)
    q1_count = len(source_q1)
    stage_count = torsion_count + q1_count
    stage_indices = correction_indices[:stage_count]
    stage_q0_block = boundary.matrix_from_rows_and_columns(
        stage_indices, target_q0)
    q0_block = boundary.matrix_from_rows_and_columns(source_q0, target_q0)
    initial_q0_syndrome = vector(
        field, [initial_boundary[index] for index in target_q0])
    vertex_syndrome = (
        initial_q0_syndrome + q1_particular * stage_q0_block)
    try:
        q0_block.solve_left(-vertex_syndrome)
        vertex_solvable_without_horizontal_adjustment = True
    except ValueError:
        vertex_solvable_without_horizontal_adjustment = False

    full_stage_local = correction[:stage_count]
    horizontal_adjustment = full_stage_local - q1_particular
    if horizontal_adjustment * q1_with_torsion:
        raise AssertionError("the horizontal adjustment is not a vertical cycle")
    q0_local = correction[stage_count:]
    if (initial_q0_syndrome
            + full_stage_local * stage_q0_block
            + q0_local * q0_block):
        raise AssertionError("the lower filtered correction does not cancel")

    torsion_local = correction[:torsion_count]
    q1_local = correction[torsion_count:torsion_count + q1_count]
    first_q0 = q0_local[:degree]
    return {
        "q1_solvable_without_orientation_torsion": (
            q1_augmented_rank == q1_rank),
        "q1_solvable_with_orientation_torsion": True,
        "total_lift_solvable": True,
        "compact_support": len(compact_lift.support()),
        "q1_syndrome_support": len(q1_syndrome.support()),
        "q1_particular_support": len(q1_particular.support()),
        "vertex_syndrome_support_before_horizontal_adjustment": len(
            vertex_syndrome.support()),
        "direct_higher_vertex_syndrome_support": len(
            initial_q0_syndrome.support()),
        "vertex_solvable_without_horizontal_adjustment": (
            vertex_solvable_without_horizontal_adjustment),
        "horizontal_vertical_cycle_adjustment_support": len(
            horizontal_adjustment.support()),
        "q1_block_rank": q1_rank,
        "q1_augmented_rank": q1_augmented_rank,
        "q2_orientation_torsion_correction_support": len(torsion_local.support()),
        "q1_correction_support": len(q1_local.support()),
        "q0_correction_support": len(q0_local.support()),
        "total_lift_support": len(total_lift.support()),
        "first_q0_generator_support": len(first_q0.support()),
        "first_q0_generator_coordinates": list(first_q0.support()),
        "exceptional_singleton_coefficient": int(first_q0[0]),
        "ordinary_singleton_coefficient": int(first_q0[1]),
    }, total_lift, vertex_syndrome


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("compact_export", type=Path)
    parser.add_argument("full_prefix", type=Path)
    parser.add_argument("harmonic_basis", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--characteristic", type=int, default=2)
    args = parser.parse_args()

    prime, degree, orbit_dimensions, cells = parse(args.compact_export)
    compact_dimensions, compact_boundaries = build_boundaries(
        degree, orbit_dimensions, cells)
    representatives = compact_representatives(degree, cells)
    if len(representatives) != compact_dimensions[2]:
        raise AssertionError("compact representative count is wrong")

    field = GF(args.characteristic)
    full_boundary = read_boundary(
        Path(str(args.full_prefix) + "-d2.tsv"), field)
    if full_boundary.nrows() != 10 * degree or full_boundary.ncols() != 4 * degree:
        raise AssertionError("unexpected full HAP dimensions")

    harmonic_rows = read_harmonic_basis(
        args.harmonic_basis, compact_dimensions[2])
    compact_boundary = compact_boundaries[2].change_ring(field)
    candidate_generator_orders = ((8, 9), (9, 8))
    comparison_ranks = {}
    cell_generators = None
    for candidate in candidate_generator_orders:
        induced = induced_compact_boundary(
            full_boundary, degree, cells, representatives, candidate)
        difference_rank = int((induced - compact_boundary).rank())
        comparison_ranks[",".join(map(str, candidate))] = difference_rank
        if difference_rank == 0:
            cell_generators = candidate
            break
    if cell_generators is None:
        raise AssertionError(
            "HAP zero-row boundary does not match the compact boundary: "
            + repr(comparison_ranks))
    two_cell_torsion_points = [
        signed_torsion_representatives(degree, cells[(2, cell_index)])
        for cell_index in (1, 2)
    ]
    q2_torsion_source_indices = [
        cell_generators[cell_index - 1] * degree + point
        for cell_index in (1, 2)
        for point in two_cell_torsion_points[cell_index - 1]
    ]
    records = []
    compact_cycles = []
    total_lifts = []
    vertex_syndromes = []
    q1_syndromes = []
    target_q1 = coordinate_indices(1, 1, degree)
    for basis_index, integer_row in enumerate(harmonic_rows):
        compact_cycle = vector(field, integer_row)
        compact_cycles.append(compact_cycle)
        if compact_cycle * compact_boundary:
            raise AssertionError("reduced compact harmonic vector is not a cycle")
        compact_lift = vector(field, full_boundary.nrows())
        for compact_coordinate in compact_cycle.support():
            cell_index, point, source_sign = representatives[compact_coordinate]
            generator = cell_generators[cell_index - 1]
            compact_lift[generator * degree + point] += (
                field(source_sign) * compact_cycle[compact_coordinate])
        initial_boundary = compact_lift * full_boundary
        q1_syndromes.append(vector(
            field, [initial_boundary[index] for index in target_q1]))
        record, total_lift, vertex_syndrome = solve_filtered_lift(
            full_boundary,
            degree,
            compact_lift,
            q2_torsion_source_indices,
        )
        record["basis_index"] = basis_index
        record["compact_reduced_support"] = len(compact_cycle.support())
        records.append(record)
        total_lifts.append(total_lift)
        vertex_syndromes.append(vertex_syndrome)

    source_q1 = coordinate_indices(2, 1, degree)
    q1_block = full_boundary.matrix_from_rows_and_columns(source_q1, target_q1)
    harmonic_q1_transgression_rank = int(
        q1_block.stack(matrix(field, q1_syndromes)).rank()
        - q1_block.rank())

    harmonic_vertex_class_rank = None
    if all(syndrome is not None for syndrome in vertex_syndromes):
        target_q0 = coordinate_indices(1, 0, degree)
        source_q0 = coordinate_indices(2, 0, degree)
        q0_block = full_boundary.matrix_from_rows_and_columns(
            source_q0, target_q0)
        harmonic_vertex_class_rank = int(
            q0_block.stack(matrix(field, vertex_syndromes)).rank()
            - q0_block.rank())

    harmonic_section_profiles = []
    harmonic_section_maximum = Fraction(0)
    if all(lift is not None for lift in total_lifts):
        for mask in range(1, 1 << len(compact_cycles)):
            compact_combination = vector(field, compact_dimensions[2])
            total_combination = vector(field, full_boundary.nrows())
            for basis_index in range(len(compact_cycles)):
                if mask & (1 << basis_index):
                    compact_combination += compact_cycles[basis_index]
                    total_combination += total_lifts[basis_index]
            compact_support = len(compact_combination.support())
            total_support = len(total_combination.support())
            if compact_support == 0:
                raise AssertionError("harmonic basis is dependent modulo the field")
            squared_ratio = Fraction(
                total_support * compact_dimensions[2],
                compact_support * full_boundary.nrows(),
            )
            harmonic_section_maximum = max(
                harmonic_section_maximum, squared_ratio)
            harmonic_section_profiles.append({
                "basis_mask": mask,
                "compact_support": compact_support,
                "total_lift_support": total_support,
                "normalized_squared_ratio": str(squared_ratio),
                "normalized_ratio_approx": float(squared_ratio ** Fraction(1, 2)),
            })

    payload = {
        "prime": prime,
        "projective_degree": degree,
        "characteristic": args.characteristic,
        "compact_degree_two_dimension": compact_dimensions[2],
        "full_degree_two_dimension": full_boundary.nrows(),
        "canonical_representative_count": len(representatives),
        "cell_generators": list(cell_generators),
        "two_cell_orientation_torsion_orbits": [
            len(points) for points in two_cell_torsion_points],
        "harmonic_q1_transgression_rank_without_orientation_torsion": (
            harmonic_q1_transgression_rank),
        "harmonic_vertex_class_rank_before_horizontal_adjustment": (
            harmonic_vertex_class_rank),
        "harmonic_modular_section_profiles": harmonic_section_profiles,
        "harmonic_modular_section_norm": {
            "squared": str(harmonic_section_maximum),
            "approx": float(harmonic_section_maximum ** Fraction(1, 2)),
        } if harmonic_section_profiles else None,
        "zero_row_comparison_ranks": comparison_ranks,
        "records": records,
    }
    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    args.output.write_text(encoded, encoding="utf-8")
    print(encoded, end="")
    print("sha256=" + hashlib.sha256(encoded.encode("utf-8")).hexdigest())


if __name__ == "__main__":
    main()
