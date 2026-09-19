"""Reduce the level-p harmonic lift in the saturated cellular range lattice.

The main cellular analyzer constructs a valid integral lift using a right
inverse for all cycle pairings.  Its quick range reduction uses raw boundary
rows, which need not generate the saturated lattice

    span_Q(rows(d2^T)) intersect Z^C2.

This Sage program computes that saturation exactly, LLL/BKZ-reduces it, and
uses deterministic approximate CVP followed by exact coordinate descent to
produce a better certified lift of the shortest harmonic Q-sharp vector.
The result is an upper bound; the independent integral-energy lower bound is
recorded alongside it.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from sage.all import QQ, ZZ, identity_matrix, lcm, matrix, vector
from sage.modules.free_module_integer import IntegerLattice

from sl3_projective_cellular_analyze import (
    build_boundaries,
    gauss_reduce_gram,
    parse,
)


def norm_squared(value):
    return value.dot_product(value)


def coordinate_descent(target, initial, basis):
    """Improve a lattice point using exact one-coordinate minimizations."""

    candidate = vector(ZZ, initial)
    residual = target - candidate
    passes = 0
    while True:
        changed = False
        passes += 1
        for row in basis.rows():
            denominator = norm_squared(row)
            step = ZZ((residual.dot_product(row) / denominator).round())
            if not step:
                continue
            new_residual = residual - step * row
            if norm_squared(new_residual) < norm_squared(residual):
                candidate += step * row
                residual = new_residual
                changed = True
        if not changed:
            return candidate, passes


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("lift_output", type=Path)
    parser.add_argument("--bkz-block-size", type=int, default=0)
    args = parser.parse_args()

    prime, degree, orbit_dimensions, cells = parse(args.input)
    dimensions, boundaries = build_boundaries(
        degree, orbit_dimensions, cells)
    d2_integer = boundaries[2].change_ring(ZZ)
    d3_integer = boundaries[3].change_ring(ZZ)

    harmonic_system = boundaries[2].transpose().stack(boundaries[3])
    harmonic_basis = matrix(
        ZZ, harmonic_system.change_ring(ZZ).right_kernel_matrix(),
        sparse=False).LLL()
    if harmonic_system * harmonic_basis.transpose() != 0:
        raise AssertionError("harmonic basis has a nonzero residual")
    if harmonic_basis.nrows() != 2:
        raise AssertionError("this reducer requires harmonic rank two")

    cycle_basis = d2_integer.transpose().right_kernel_matrix()
    pairing_lattice = (
        harmonic_basis * cycle_basis.transpose()).transpose().row_module()
    pairing_basis = pairing_lattice.basis_matrix()
    qsharp_coordinates = pairing_basis.transpose().inverse()
    qsharp_basis = qsharp_coordinates * harmonic_basis
    qsharp_pairings = qsharp_basis * cycle_basis.transpose()
    if any(value.denominator() != 1 for value in qsharp_pairings.list()):
        raise AssertionError("Q-sharp vector has a nonintegral cycle pairing")
    qsharp_pairings = qsharp_pairings.change_ring(ZZ)

    harmonic_in_qsharp = qsharp_coordinates.inverse()
    if any(value.denominator() != 1 for value in harmonic_in_qsharp.list()):
        raise AssertionError("harmonic lattice is not integral in Q-sharp")
    harmonic_in_qsharp = harmonic_in_qsharp.change_ring(ZZ)
    qsharp_reduction, reduced_gram = gauss_reduce_gram(
        qsharp_basis * qsharp_basis.transpose())
    shortest_coordinates = vector(ZZ, qsharp_reduction.row(0))
    shortest_qsharp = shortest_coordinates * qsharp_basis
    quotient_coordinates = (
        shortest_coordinates * harmonic_in_qsharp.change_ring(QQ).inverse())
    shortest_order = int(lcm(
        value.denominator() for value in quotient_coordinates))
    shortest_squared = norm_squared(shortest_qsharp)

    cycle_hnf, cycle_transform = cycle_basis.transpose().hermite_form(
        transformation=True, include_zero_rows=True)
    cycle_rank = cycle_basis.nrows()
    if cycle_hnf[:cycle_rank, :] != identity_matrix(ZZ, cycle_rank):
        raise AssertionError("cycle lattice is not primitive")
    cycle_right_inverse = cycle_transform.transpose()[:, :cycle_rank]
    if cycle_basis * cycle_right_inverse != identity_matrix(ZZ, cycle_rank):
        raise AssertionError("invalid cycle-pairing right inverse")
    lift_basis = (
        cycle_right_inverse * qsharp_pairings.transpose()).transpose()
    raw_lift = shortest_coordinates * lift_basis
    if d3_integer * raw_lift.column() != 0:
        raise AssertionError("raw lift is not a cocycle")

    raw_range_module = d2_integer.transpose().row_module()
    raw_range_index = int(raw_range_module.index_in_saturation())
    saturated_range = raw_range_module.saturation()
    if saturated_range.index_in_saturation() != 1:
        raise AssertionError("range saturation is not primitive")
    saturated_basis = matrix(
        ZZ, saturated_range.basis_matrix(), sparse=False)
    reduced_basis = saturated_basis.LLL(delta=0.99)
    if args.bkz_block_size:
        reduced_basis = reduced_basis.BKZ(
            block_size=args.bkz_block_size, proof=False)
    lattice = IntegerLattice(reduced_basis, lll_reduce=False)

    target = raw_lift.change_ring(QQ) - shortest_qsharp
    candidates = []
    for algorithm in ("nearest_plane", "rounding_off"):
        candidate = lattice.approximate_closest_vector(
            target, algorithm=algorithm)
        candidate, passes = coordinate_descent(target, candidate, reduced_basis)
        if candidate not in saturated_range:
            raise AssertionError("CVP candidate left the saturated range")
        candidates.append((norm_squared(target - candidate), algorithm,
                           passes, candidate))
    _, algorithm, passes, closest = min(candidates, key=lambda item: item[0])

    reduced_lift = raw_lift - closest
    if d3_integer * reduced_lift.column() != 0:
        raise AssertionError("reduced lift is not a cocycle")
    if reduced_lift * cycle_basis.transpose() != (
            shortest_qsharp * cycle_basis.transpose()):
        raise AssertionError("range reduction changed the harmonic projection")
    lift_squared = norm_squared(reduced_lift)
    if lift_squared not in ZZ or lift_squared <= 0:
        raise AssertionError("integral lift energy is not a positive integer")
    range_squared = lift_squared - shortest_squared
    distortion_squared = lift_squared / shortest_squared

    digest = hashlib.sha256()
    with args.lift_output.open("w", encoding="ascii") as stream:
        header = "coordinate qsharp lift\n"
        stream.write(header)
        digest.update(header.encode("ascii"))
        for coordinate, (qsharp_value, lift_value) in enumerate(zip(
                shortest_qsharp, reduced_lift)):
            line = f"{coordinate} {qsharp_value} {lift_value}\n"
            stream.write(line)
            digest.update(line.encode("ascii"))

    result = {
        "prime": prime,
        "ambient_dimension": dimensions[2],
        "range_rank": int(saturated_range.rank()),
        "raw_boundary_range_index_in_saturation": raw_range_index,
        "saturated_basis_maximum_absolute_coefficient": max(
            abs(int(value)) for value in saturated_basis.list()),
        "reduction_basis": (
            f"BKZ-{args.bkz_block_size}" if args.bkz_block_size else "LLL"),
        "selected_cvp_algorithm": algorithm,
        "coordinate_descent_passes": passes,
        "shortest_class_order": shortest_order,
        "shortest_qsharp_squared_norm": str(shortest_squared),
        "integral_energy_lower_bound": "1",
        "distortion_lower_bound_squared": str(1 / shortest_squared),
        "certified_lift_squared_norm": str(lift_squared),
        "certified_range_squared_norm": str(range_squared),
        "certified_distortion_upper_squared": str(distortion_squared),
        "lift_sha256": digest.hexdigest(),
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
