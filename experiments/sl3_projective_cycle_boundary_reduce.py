"""Shorten exact projective two-cycles by adding integral boundaries.

The input packet contains literal integral cycles.  Rows of ``d_3`` are
literal integral boundaries, so adding any vector in their integer row
lattice preserves the homology class.  This MSI-only experiment selects a
rationally independent set of boundary rows, LLL-reduces their lattice, and
uses Babai reduction in each packet coset.  Every output representative is
verified exactly against ``d_2^T`` and against the selected boundary lattice.

This gives certified upper bounds for integral lift norms.  Because the
selected rows need not generate the saturated boundary lattice, failure to
find a short representative is not a lower bound.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from pathlib import Path

from fpylll import GSO, IntegerMatrix, LLL
from sage.all import GF, ZZ, matrix, vector

from sl3_projective_cellular_analyze import build_boundaries, parse


def to_fpylll(basis):
    result = IntegerMatrix(basis.nrows(), basis.ncols())
    for row in range(basis.nrows()):
        for column in range(basis.ncols()):
            result[row, column] = int(basis[row, column])
    return result


def sparse_entries(candidate):
    return [
        {"coordinate": int(index), "coefficient": int(value)}
        for index, value in enumerate(candidate) if value
    ]


def statistics(candidate):
    nonzero = [abs(int(value)) for value in candidate if value]
    return {
        "support_size": len(nonzero),
        "l1": sum(nonzero),
        "l2_squared": sum(value * value for value in nonzero),
        "maximum_absolute_coefficient": max(nonzero, default=0),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("cellular_input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument(
        "--packet", type=Path, action="append", required=True,
        help="exact circuit packet; repeat to combine coordinate orders")
    parser.add_argument("--characteristic", type=int, default=1009)
    parser.add_argument("--delta", type=float, default=0.99)
    args = parser.parse_args()

    started = time.monotonic()
    level, degree, orbit_dimensions, cells = parse(args.cellular_input)
    dimensions, boundaries = build_boundaries(
        degree, orbit_dimensions, cells)
    packet_sources = []
    packet_hashes = {}
    seen_cycles = set()
    for packet_path in args.packet:
        packet_bytes = packet_path.read_bytes()
        packet_hashes[str(packet_path)] = hashlib.sha256(packet_bytes).hexdigest()
        packet = json.loads(packet_bytes)
        if packet["level"] != level:
            raise ValueError("packet and cellular complex have different levels")
        for source in packet["exact_short_homology_circuits"]:
            key = tuple(
                (entry["coordinate"], entry["coefficient"])
                for entry in source["coordinates"])
            if key in seen_cycles:
                continue
            seen_cycles.add(key)
            packet_sources.append((str(packet_path), source))

    cycle_matrix = boundaries[2].transpose().change_ring(ZZ)
    boundary_matrix = boundaries[3].change_ring(ZZ)
    field = GF(args.characteristic)
    reduced_boundary = boundary_matrix.change_ring(field)
    pivot_rows = list(reduced_boundary.transpose().pivots())
    if len(pivot_rows) != reduced_boundary.rank():
        raise AssertionError("failed to select independent boundary rows")
    boundary_basis = boundary_matrix.matrix_from_rows(pivot_rows)
    if boundary_basis.rank() != len(pivot_rows):
        raise AssertionError("selected boundary rows are rationally dependent")
    if cycle_matrix * boundary_basis.transpose() != 0:
        raise AssertionError("a selected boundary row is not a cycle")

    modular_cycle_matrix = cycle_matrix.change_ring(field)
    modular_cycle_basis = modular_cycle_matrix.right_kernel_matrix()
    cycle_pivots = list(modular_cycle_basis.pivots())
    cycle_pivot_minor_inverse = modular_cycle_basis.matrix_from_columns(
        cycle_pivots).inverse()
    boundary_cycle_coordinates = (
        reduced_boundary.matrix_from_columns(cycle_pivots)
        * cycle_pivot_minor_inverse)
    if boundary_cycle_coordinates * modular_cycle_basis != reduced_boundary:
        raise AssertionError("failed to coordinatize modular boundaries")
    quotient_dual = boundary_cycle_coordinates.right_kernel_matrix()
    homology_dimension = int(quotient_dual.nrows())

    reduced_basis = to_fpylll(boundary_basis)
    print(
        f"level={level} boundaries={boundary_basis.nrows()}x"
        f"{boundary_basis.ncols()} delta={args.delta}", flush=True)
    LLL.reduction(reduced_basis, delta=args.delta)
    gram_schmidt = GSO.Mat(reduced_basis)
    gram_schmidt.update_gso()
    print(f"lll_seconds={time.monotonic() - started:.6f}", flush=True)

    records = []
    reduced_vectors = []
    for packet_index, (packet_path, source) in enumerate(packet_sources):
        initial = vector(ZZ, dimensions[2])
        for entry in source["coordinates"]:
            initial[entry["coordinate"]] = entry["coefficient"]
        if cycle_matrix * initial.column() != 0:
            raise AssertionError("packet input contains a noncycle")

        babai_coefficients = gram_schmidt.babai(
            tuple(-int(value) for value in initial))
        boundary = vector(
            ZZ, reduced_basis.multiply_left(babai_coefficients))
        candidate = initial + boundary
        if cycle_matrix * candidate.column() != 0:
            raise AssertionError("boundary reduction produced a noncycle")
        initial_statistics = statistics(initial)
        candidate_statistics = statistics(candidate)
        if candidate_statistics["l2_squared"] > initial_statistics["l2_squared"]:
            candidate = initial
            boundary = vector(ZZ, dimensions[2])
            candidate_statistics = initial_statistics
        record = {
            "packet_index": packet_index,
            "packet_source": packet_path,
            "kernel_row": source["kernel_row"],
            "initial": initial_statistics,
            "reduced": candidate_statistics,
            "improved": (
                candidate_statistics["l2_squared"]
                < initial_statistics["l2_squared"]),
            "representative": sparse_entries(candidate),
            "added_boundary": sparse_entries(boundary),
        }
        records.append(record)
        reduced_vectors.append(candidate)
        print(json.dumps({
            "packet_index": packet_index,
            "initial": initial_statistics,
            "reduced": candidate_statistics,
        }, sort_keys=True), flush=True)

    signatures = []
    for candidate in reduced_vectors:
        cycle_coordinates = (
            vector(field, [candidate[column] for column in cycle_pivots])
            * cycle_pivot_minor_inverse)
        signatures.append(quotient_dual * cycle_coordinates.column())

    selected_indices = []
    selected_signatures = []
    selected_rank = 0
    for index in sorted(
            range(len(records)),
            key=lambda item: (
                records[item]["reduced"]["l2_squared"],
                records[item]["reduced"]["support_size"], item)):
        candidate_signatures = selected_signatures + [
            list(signatures[index].column(0))]
        candidate_rank = matrix(field, candidate_signatures).rank()
        if candidate_rank == selected_rank:
            continue
        selected_indices.append(index)
        selected_signatures.append(list(signatures[index].column(0)))
        selected_rank = candidate_rank
        if selected_rank == homology_dimension:
            break
    if selected_rank != homology_dimension:
        raise AssertionError("combined reduced packets do not span homology")

    selected_vectors = [reduced_vectors[index] for index in selected_indices]
    reduced_gram = matrix(ZZ, [
        [left.dot_product(right) for right in reduced_vectors]
        for left in reduced_vectors
    ])
    absolute_gram_row_sums = [
        sum(abs(int(value)) for value in row)
        for row in reduced_gram.rows()
    ]
    selected_gram = matrix(ZZ, [
        [left.dot_product(right) for right in selected_vectors]
        for left in selected_vectors
    ])
    selected_absolute_gram_row_sums = [
        sum(abs(int(value)) for value in row)
        for row in selected_gram.rows()
    ]
    certificate = {
        "level": level,
        "projective_degree": degree,
        "rational_coinvariant_dimensions": dimensions,
        "packet_source_sha256": packet_hashes,
        "characteristic": args.characteristic,
        "boundary_matrix_rank_mod_characteristic": int(
            reduced_boundary.rank()),
        "selected_boundary_row_count": len(pivot_rows),
        "selected_boundary_rows": [int(row) for row in pivot_rows],
        "homology_dimension_mod_characteristic": homology_dimension,
        "lll_delta": args.delta,
        "records": records,
        "maximum_initial_squared_norm": max(
            record["initial"]["l2_squared"] for record in records),
        "maximum_reduced_squared_norm": max(
            record["reduced"]["l2_squared"] for record in records),
        "maximum_reduced_support": max(
            record["reduced"]["support_size"] for record in records),
        "maximum_reduced_coefficient": max(
            record["reduced"]["maximum_absolute_coefficient"]
            for record in records),
        "reduced_packet_gram": [
            [int(value) for value in row] for row in reduced_gram.rows()],
        "reduced_packet_absolute_gram_row_sums": absolute_gram_row_sums,
        "maximum_reduced_packet_absolute_gram_row_sum": max(
            absolute_gram_row_sums),
        "shortest_spanning_packet_indices": selected_indices,
        "shortest_spanning_packet_gram": [
            [int(value) for value in row] for row in selected_gram.rows()],
        "shortest_spanning_packet_absolute_gram_row_sums": (
            selected_absolute_gram_row_sums),
        "shortest_spanning_packet_maximum_squared_norm": max(
            records[index]["reduced"]["l2_squared"]
            for index in selected_indices),
        "shortest_spanning_packet_maximum_support": max(
            records[index]["reduced"]["support_size"]
            for index in selected_indices),
        "shortest_spanning_packet_maximum_coefficient": max(
            records[index]["reduced"]["maximum_absolute_coefficient"]
            for index in selected_indices),
        "shortest_spanning_packet_maximum_absolute_gram_row_sum": max(
            selected_absolute_gram_row_sums),
        "elapsed_seconds": time.monotonic() - started,
        "scope": (
            "certified upper bounds in cosets of the selected integral "
            "boundary-row lattice; not CVP optima or lower bounds"),
    }
    rendered = json.dumps(certificate, indent=2, sort_keys=True) + "\n"
    args.output.write_text(rendered, encoding="utf-8")


if __name__ == "__main__":
    main()
