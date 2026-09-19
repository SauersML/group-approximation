"""Screen a projective cellular cycle kernel for short fundamental circuits.

This is a finite-field discriminator, not an integral certificate.  The
right-kernel echelon basis records the fundamental dependencies selected by
the sparse modular elimination.  Small balanced coefficients and bounded
row supports are evidence for the exact certificate in
``TRUE_FUNDAMENTAL_CIRCUIT_PACKET_CERTIFICATE.md``; dense rows or large
balanced coefficients only show that this particular pivot choice fails.

Run with Sage's Python on MSI, not with a local Python interpreter.
"""

from __future__ import annotations

import argparse
import json
import random
from pathlib import Path

from sage.all import GF, ZZ, gcd, matrix, vector

from sl3_projective_cellular_analyze import build_boundaries, coinvariants, parse


def quantiles(values: list[int]) -> dict[str, int]:
    ordered = sorted(values)
    if not ordered:
        return {"minimum": 0, "median": 0, "p90": 0, "p99": 0, "maximum": 0}

    def select(numerator: int, denominator: int) -> int:
        index = ((len(ordered) - 1) * numerator) // denominator
        return int(ordered[index])

    return {
        "minimum": int(ordered[0]),
        "median": select(1, 2),
        "p90": select(9, 10),
        "p99": select(99, 100),
        "maximum": int(ordered[-1]),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--characteristic", type=int, default=1009)
    parser.add_argument("--expected-rank", type=int)
    parser.add_argument(
        "--reverse-columns", action="store_true",
        help="reverse the degree-two coordinate order before echelon reduction")
    parser.add_argument(
        "--column-seed", type=int,
        help="deterministically shuffle degree-two coordinates before reduction")
    parser.add_argument(
        "--exact-support-limit", type=int, default=64,
        help="lift selected modular circuits up to this support size over Z")
    args = parser.parse_args()

    field = GF(args.characteristic)
    level, degree, orbit_dimensions, cells = parse(args.input)
    dimensions, boundaries = build_boundaries(degree, orbit_dimensions, cells)

    original_cycle_matrix = boundaries[2].transpose().change_ring(field)
    column_order = list(range(original_cycle_matrix.ncols()))
    if args.reverse_columns and args.column_seed is not None:
        parser.error("--reverse-columns and --column-seed are mutually exclusive")
    if args.reverse_columns:
        column_order.reverse()
    elif args.column_seed is not None:
        random.Random(args.column_seed).shuffle(column_order)
    cycle_matrix = original_cycle_matrix.matrix_from_columns(column_order)
    print(
        f"level={level} matrix={cycle_matrix.nrows()}x{cycle_matrix.ncols()} "
        f"characteristic={args.characteristic}",
        flush=True,
    )
    kernel = cycle_matrix.right_kernel_matrix()
    rank = cycle_matrix.ncols() - kernel.nrows()
    if args.expected_rank is not None and rank != args.expected_rank:
        raise AssertionError(
            f"modular rank {rank} differs from expected rank {args.expected_rank}")
    if cycle_matrix * kernel.transpose() != 0:
        raise AssertionError("kernel basis has a nonzero residual")

    support_sizes = []
    balanced_l1 = []
    balanced_l2_squared = []
    balanced_maximum = []
    coefficients = 0
    coefficients_of_size_one = 0
    for row in kernel.rows():
        balanced = []
        for value in row:
            integer = int(value)
            if integer == 0:
                continue
            representative = min(integer, args.characteristic - integer)
            balanced.append(representative)
        support_sizes.append(len(balanced))
        balanced_l1.append(sum(balanced))
        balanced_l2_squared.append(sum(value * value for value in balanced))
        balanced_maximum.append(max(balanced, default=0))
        coefficients += len(balanced)
        coefficients_of_size_one += sum(value == 1 for value in balanced)

    boundary_matrix = boundaries[3].change_ring(field).matrix_from_columns(
        column_order)
    if cycle_matrix * boundary_matrix.transpose() != 0:
        raise AssertionError("cellular boundaries are not cycles")
    kernel_pivots = list(kernel.pivots())
    if len(kernel_pivots) != kernel.nrows():
        raise AssertionError("kernel basis does not have enough pivot columns")
    pivot_minor = kernel.matrix_from_columns(kernel_pivots)
    boundary_coordinates = (
        boundary_matrix.matrix_from_columns(kernel_pivots)
        * pivot_minor.inverse()
    )
    if boundary_coordinates * kernel != boundary_matrix:
        raise AssertionError("failed to express boundaries in cycle coordinates")
    quotient_dual = boundary_coordinates.right_kernel_matrix()
    homology_dimension = int(quotient_dual.nrows())

    selected_rows = []
    selected_signatures = []
    order = sorted(
        range(kernel.nrows()),
        key=lambda index: (
            support_sizes[index], balanced_l2_squared[index],
            balanced_l1[index], index),
    )
    signature_rank = 0
    for index in order:
        signature = list(quotient_dual.column(index))
        candidate_rank = matrix(
            field, selected_signatures + [signature]).rank()
        if candidate_rank == signature_rank:
            continue
        selected_signatures.append(signature)
        selected_rows.append({
            "kernel_row": int(index),
            "support_size": int(support_sizes[index]),
            "balanced_l1": int(balanced_l1[index]),
            "balanced_l2_squared": int(balanced_l2_squared[index]),
            "balanced_maximum_coefficient": int(balanced_maximum[index]),
        })
        signature_rank = candidate_rank
        if signature_rank == homology_dimension:
            break
    if signature_rank != homology_dimension:
        raise AssertionError("fundamental circuits do not span homology")

    exact_short_circuits = []
    exact_short_vectors = []
    rational_cycle_matrix = boundaries[2].transpose().matrix_from_columns(
        column_order)
    degree_two_coordinates = {}
    degree_two_offset = 0
    for cell_orbit in range(1, orbit_dimensions[2] + 1):
        coinvariant_dimension, coordinate_map = coinvariants(
            degree, cells[(2, cell_orbit)])
        representatives = {}
        for projective_point, value in enumerate(coordinate_map):
            if value is None:
                continue
            local_coordinate, orientation = value
            representatives.setdefault(
                local_coordinate, (projective_point, orientation))
        for local_coordinate, value in representatives.items():
            projective_point, orientation = value
            degree_two_coordinates[degree_two_offset + local_coordinate] = {
                "cell_orbit": int(cell_orbit),
                "cell_orbit_coordinate": int(local_coordinate),
                "projective_point_index": int(projective_point),
                "coinvariant_orientation": int(orientation),
            }
        degree_two_offset += coinvariant_dimension
    if degree_two_offset != rational_cycle_matrix.ncols():
        raise AssertionError("degree-two coordinate decoder has the wrong size")
    for selected in selected_rows:
        index = selected["kernel_row"]
        if selected["support_size"] > args.exact_support_limit:
            continue
        support = [
            column for column, value in enumerate(kernel.row(index)) if value]
        subsystem = rational_cycle_matrix.matrix_from_columns(support)
        exact_kernel = subsystem.change_ring(ZZ).right_kernel_matrix()
        if exact_kernel.nrows() != 1:
            raise AssertionError(
                "short modular circuit does not have a unique rational lift")
        exact_coefficients = [ZZ(value) for value in exact_kernel.row(0)]
        common = gcd(exact_coefficients)
        exact_coefficients = [value // common for value in exact_coefficients]
        first = next(value for value in exact_coefficients if value)
        if first < 0:
            exact_coefficients = [-value for value in exact_coefficients]
        if subsystem * vector(ZZ, exact_coefficients) != 0:
            raise AssertionError("exact short circuit has a nonzero residual")
        full_exact_circuit = vector(ZZ, rational_cycle_matrix.ncols())
        for column, coefficient in zip(support, exact_coefficients):
            full_exact_circuit[column_order[column]] = coefficient
        exact_short_vectors.append(full_exact_circuit)

        modular_row = kernel.row(index)
        pivot = next(
            offset for offset, value in enumerate(exact_coefficients)
            if field(value) != 0)
        scalar = (
            field(exact_coefficients[pivot]) / modular_row[support[pivot]])
        if any(
                field(coefficient) != scalar * modular_row[column]
                for column, coefficient in zip(support, exact_coefficients)):
            raise AssertionError(
                "exact short circuit does not reduce to the modular circuit")
        exact_short_circuits.append({
            "kernel_row": int(index),
            "support_size": len(support),
            "l1": int(sum(abs(value) for value in exact_coefficients)),
            "l2_squared": int(sum(
                value * value for value in exact_coefficients)),
            "maximum_absolute_coefficient": int(max(
                abs(value) for value in exact_coefficients)),
            "primitive": gcd(exact_coefficients) == 1,
            "modular_homology_signature_nonzero": any(
                quotient_dual[row, index] != 0
                for row in range(quotient_dual.nrows())),
            "coordinates": [
                {
                    "coordinate": int(column_order[column]),
                    "coefficient": int(coefficient),
                    **degree_two_coordinates[column_order[column]],
                }
                for column, coefficient in zip(support, exact_coefficients)
            ],
        })

    certificate = {
        "level": int(level),
        "projective_degree": int(degree),
        "cell_orbit_dimensions": orbit_dimensions,
        "rational_coinvariant_dimensions": dimensions,
        "characteristic": int(args.characteristic),
        "column_order": (
            "reverse" if args.reverse_columns else
            f"shuffle:{args.column_seed}" if args.column_seed is not None else
            "natural"),
        "exact_support_limit": int(args.exact_support_limit),
        "cycle_matrix_dimensions": [
            int(cycle_matrix.nrows()), int(cycle_matrix.ncols())],
        "cycle_matrix_rank": int(rank),
        "kernel_dimension": int(kernel.nrows()),
        "boundary_rank": int(boundary_coordinates.rank()),
        "homology_dimension": homology_dimension,
        "kernel_residual_zero": True,
        "basis_role": (
            "finite-field right-kernel echelon basis; a pivot-choice screen, "
            "not an integral fundamental-circuit certificate"),
        "support_size": quantiles(support_sizes),
        "balanced_l1": quantiles(balanced_l1),
        "balanced_l2_squared": quantiles(balanced_l2_squared),
        "balanced_maximum_coefficient": quantiles(balanced_maximum),
        "nonzero_coefficient_count": int(coefficients),
        "balanced_unit_coefficient_count": int(coefficients_of_size_one),
        "balanced_unit_coefficient_fraction": (
            coefficients_of_size_one / coefficients if coefficients else 1.0),
        "greedy_homology_packet": selected_rows,
        "greedy_homology_packet_maximum_support": max(
            (row["support_size"] for row in selected_rows), default=0),
        "greedy_homology_packet_maximum_balanced_l2_squared": max(
            (row["balanced_l2_squared"] for row in selected_rows), default=0),
        "exact_short_homology_circuits": exact_short_circuits,
        "exact_short_packet_gram": [
            [int(left * right) for right in exact_short_vectors]
            for left in exact_short_vectors
        ],
        "exact_short_packet_modular_quotient_rank": int(matrix(
            field,
            [list(quotient_dual.column(row["kernel_row"]))
             for row in exact_short_circuits],
        ).rank()) if exact_short_circuits else 0,
    }
    rendered = json.dumps(certificate, indent=2, sort_keys=True) + "\n"
    args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
