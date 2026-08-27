"""Extract a one-dimensional prime saturation direction of a boundary row lattice.

For an integral matrix ``R`` of rational row rank ``r``, suppose its row rank
drops from ``r`` to ``r-1`` modulo a prime ``p``.  Choose ``r-1`` rows which
are independent modulo ``p`` and one further row which restores rational
rank.  The unique modulo-``p`` dependence among those ``r`` rows lifts to an
integral combination divisible by ``p``.  Dividing gives a vector in

    Sat(Row_Z(R)) = Row_Q(R) intersect Z^n.

The script verifies that adjoining this vector restores full rank modulo
``p`` and exports an exact sparse certificate.  Run with Sage on MSI.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from sage.all import GF, ZZ, is_prime, matrix, vector

from sl3_projective_cellular_analyze import build_boundaries, parse


def sparse_vector_json(value):
    return [
        {"coordinate": int(index), "coefficient": int(entry)}
        for index, entry in enumerate(value) if entry
    ]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("cellular_input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--boundary-degree", type=int, default=2)
    parser.add_argument("--prime", type=int, required=True)
    parser.add_argument("--good-prime", type=int, default=101)
    args = parser.parse_args()

    if not is_prime(args.prime) or not is_prime(args.good_prime):
        parser.error("--prime and --good-prime must be prime")
    if args.prime == args.good_prime:
        parser.error("--prime and --good-prime must differ")

    input_bytes = args.cellular_input.read_bytes()
    level, degree, orbit_dimensions, cells = parse(args.cellular_input)
    dimensions, boundaries = build_boundaries(degree, orbit_dimensions, cells)
    if args.boundary_degree not in boundaries:
        parser.error("requested boundary degree is absent")
    row_matrix = boundaries[args.boundary_degree].transpose().change_ring(ZZ)

    bad_field = GF(args.prime)
    good_field = GF(args.good_prime)
    bad_matrix = row_matrix.change_ring(bad_field)
    good_matrix = row_matrix.change_ring(good_field)
    bad_rank = bad_matrix.rank()
    good_rank = good_matrix.rank()
    if good_rank - bad_rank != 1:
        raise ValueError(
            "this extractor requires an exactly one-dimensional rank drop")

    bad_row_indices = list(bad_matrix.transpose().pivots())
    if len(bad_row_indices) != bad_rank:
        raise AssertionError("failed to select the bad-field row basis")
    selected_good = good_matrix.matrix_from_rows(bad_row_indices)
    selected_good_rank = selected_good.rank()
    extra_row_index = None
    for candidate in good_matrix.transpose().pivots():
        if candidate in bad_row_indices:
            continue
        trial = selected_good.stack(good_matrix.row(candidate))
        if trial.rank() == selected_good_rank + 1:
            extra_row_index = int(candidate)
            break
    if extra_row_index is None or selected_good_rank + 1 != good_rank:
        raise AssertionError("failed to restore the good-field rank")

    selected_indices = bad_row_indices + [extra_row_index]
    selected_rows = row_matrix.matrix_from_rows(selected_indices)
    dependence_space = (
        selected_rows.transpose().change_ring(bad_field).right_kernel())
    if dependence_space.dimension() != 1:
        raise AssertionError("selected rows do not have one prime dependence")
    dependence = dependence_space.basis()[0]
    lifted_dependence = vector(
        ZZ, [int(coefficient) for coefficient in dependence])
    divisible_combination = lifted_dependence * selected_rows
    if any(entry % args.prime for entry in divisible_combination):
        raise AssertionError("lifted prime dependence is not divisible")
    saturation_direction = divisible_combination / args.prime
    if saturation_direction not in ZZ ** row_matrix.ncols():
        raise AssertionError("divided dependence is not integral")
    saturation_direction = vector(ZZ, saturation_direction)

    augmented_bad_rank = bad_matrix.stack(
        vector(bad_field, saturation_direction)).rank()
    if augmented_bad_rank != good_rank:
        raise AssertionError(
            "the divided combination did not restore full prime rank")

    coefficients = [
        abs(int(entry)) for entry in saturation_direction if entry]
    certificate = {
        "level": level,
        "projective_degree": degree,
        "rational_coinvariant_dimensions": dimensions,
        "boundary_degree": args.boundary_degree,
        "row_matrix_dimensions": list(row_matrix.dimensions()),
        "prime": args.prime,
        "good_prime": args.good_prime,
        "row_rank_mod_prime": int(bad_rank),
        "row_rank_mod_good_prime": int(good_rank),
        "augmented_row_rank_mod_prime": int(augmented_bad_rank),
        "selected_bad_field_row_indices": [
            int(index) for index in bad_row_indices],
        "extra_rational_row_index": extra_row_index,
        "lifted_dependence_coefficients": [
            int(entry) for entry in lifted_dependence],
        "saturation_direction": sparse_vector_json(saturation_direction),
        "saturation_direction_support_size": len(coefficients),
        "saturation_direction_l1": sum(coefficients),
        "saturation_direction_squared_norm": sum(
            coefficient * coefficient for coefficient in coefficients),
        "saturation_direction_maximum_absolute_coefficient": max(
            coefficients, default=0),
        "cellular_input_sha256": hashlib.sha256(input_bytes).hexdigest(),
        "proof": (
            "the selected rows have a unique dependence modulo the target "
            "prime; its integral lift is coordinatewise divisible by that "
            "prime, and the divided vector restores full modular row rank"),
    }
    args.output.write_text(
        json.dumps(certificate, indent=2, sort_keys=True) + "\n",
        encoding="utf-8")
    print(json.dumps({
        "level": level,
        "prime": args.prime,
        "row_rank_mod_prime": int(bad_rank),
        "row_rank_mod_good_prime": int(good_rank),
        "augmented_row_rank_mod_prime": int(augmented_bad_rank),
        "saturation_direction_support_size": len(coefficients),
        "saturation_direction_squared_norm": sum(
            coefficient * coefficient for coefficient in coefficients),
        "saturation_direction_maximum_absolute_coefficient": max(
            coefficients, default=0),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
