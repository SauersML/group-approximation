"""Compute an exact harmonic dual-systole screen in arbitrary rank.

This is the rank-independent, inexpensive part of the integral harmonic lift
analysis.  It reconstructs Q-sharp from any certified integral basis spanning
the rational harmonic space, computes its exact shortest vector with fplll,
and compares that vector with the spherical localization threshold.  The
input basis need not be primitive.  It deliberately does not construct an
ambient integral section; that expensive step is warranted only when the
systole screen is subthreshold.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from sage.all import ZZ, FreeModule, lcm, matrix, vector
from sage.modules.free_module_integer import IntegerLattice

from sl3_projective_cellular_analyze import build_boundaries, parse


def read_harmonic_basis(path: Path, ambient_dimension: int):
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    with path.open(encoding="ascii") as stream:
        header = stream.readline().split()
        if not header or header[0] != "coordinate":
            raise ValueError("invalid harmonic basis header")
        rank = len(header) - 1
        rows = [[] for _ in range(rank)]
        for expected_coordinate, line in enumerate(stream):
            fields = line.split()
            if len(fields) != rank + 1:
                raise ValueError("invalid harmonic basis row width")
            if int(fields[0]) != expected_coordinate:
                raise ValueError("nonconsecutive harmonic coordinate")
            for index, value in enumerate(fields[1:]):
                rows[index].append(int(value))
    if any(len(row) != ambient_dimension for row in rows):
        raise ValueError("harmonic basis has the wrong ambient dimension")
    return matrix(ZZ, rows), digest


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("harmonic_basis", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    level, degree, orbit_dimensions, cells = parse(args.input)
    dimensions, boundaries = build_boundaries(degree, orbit_dimensions, cells)
    harmonic_basis, harmonic_hash = read_harmonic_basis(
        args.harmonic_basis, dimensions[2])
    if not harmonic_basis.nrows():
        raise ValueError("the harmonic basis has rank zero")

    harmonic_system = boundaries[2].transpose().stack(boundaries[3])
    if harmonic_system * harmonic_basis.transpose() != 0:
        raise AssertionError("harmonic basis has a nonzero exact residual")

    print("systole: computing the rational cycle nullspace", flush=True)
    cycle_rational_kernel = boundaries[2].transpose().right_kernel_matrix()
    print("systole: intersecting the cycle space with the integer lattice",
          flush=True)
    cycle_lattice = cycle_rational_kernel.row_space().intersection(
        FreeModule(ZZ, dimensions[2]))
    cycle_basis = cycle_lattice.basis_matrix()
    if boundaries[2].transpose() * cycle_basis.transpose() != 0:
        raise AssertionError("cycle lattice has a nonzero exact residual")
    print("systole: reconstructing Q-sharp from cycle pairings", flush=True)
    harmonic_cycle_pairing = harmonic_basis * cycle_basis.transpose()
    pairing_basis = harmonic_cycle_pairing.transpose().row_module().basis_matrix()
    if pairing_basis.nrows() != harmonic_basis.nrows():
        raise AssertionError("harmonic pairing lattice has the wrong rank")

    qsharp_coordinates = pairing_basis.transpose().inverse()
    qsharp_basis = qsharp_coordinates * harmonic_basis
    qsharp_cycle_pairing = qsharp_basis * cycle_basis.transpose()
    if any(value.denominator() != 1 for value in qsharp_cycle_pairing.list()):
        raise AssertionError("Q-sharp has a nonintegral cycle pairing")

    qsharp_gram = qsharp_basis * qsharp_basis.transpose()
    exported_harmonic_in_qsharp = qsharp_coordinates.inverse()
    if any(value.denominator() != 1
           for value in exported_harmonic_in_qsharp.list()):
        raise AssertionError(
            "exported integral harmonic vectors have nonintegral "
            "Q-sharp coordinates")
    exported_harmonic_in_qsharp = exported_harmonic_in_qsharp.change_ring(ZZ)

    common_denominator = int(qsharp_basis.denominator())
    scaled_basis = (common_denominator * qsharp_basis).change_ring(ZZ)
    print("systole: solving the exact shortest-vector problem", flush=True)
    lattice = IntegerLattice(scaled_basis, lll_reduce=True)
    shortest_scaled = vector(ZZ, lattice.shortest_vector())
    scaled_gram = scaled_basis * scaled_basis.transpose()
    shortest_coordinates = (
        shortest_scaled * scaled_basis.transpose() * scaled_gram.inverse())
    if any(value.denominator() != 1 for value in shortest_coordinates):
        raise AssertionError("shortest Q-sharp vector has nonintegral coordinates")
    shortest_coordinates = vector(ZZ, shortest_coordinates)
    shortest_qsharp = shortest_coordinates * qsharp_basis
    shortest_squared_norm = shortest_qsharp.dot_product(shortest_qsharp)
    if shortest_scaled.dot_product(shortest_scaled) != (
            common_denominator**2 * shortest_squared_norm):
        raise AssertionError("scaled shortest-vector norm mismatch")

    shortest_is_integral_harmonic = all(
        value.denominator() == 1 for value in shortest_qsharp)
    shortest_class_order = int(lcm(
        value.denominator() for value in shortest_qsharp))
    spherical_template_max_squared_norm = max(
        sum(value * value for value in boundaries[3].row(row))
        for row in range(boundaries[3].nrows()))

    certificate = {
        "level": level,
        "projective_degree": degree,
        "cell_orbit_dimensions": orbit_dimensions,
        "rational_coinvariant_dimensions": dimensions,
        "harmonic_rank": int(harmonic_basis.nrows()),
        "harmonic_basis_sha256": harmonic_hash,
        "cycle_lattice_rank": int(cycle_basis.nrows()),
        "pairing_lattice_basis": [
            [int(value) for value in row] for row in pairing_basis.rows()],
        "qsharp_maximum_numerator": max(
            abs(int(value.numerator())) for value in qsharp_basis.list()),
        "qsharp_common_denominator": common_denominator,
        "qsharp_gram": [
            [str(value) for value in row] for row in qsharp_gram.rows()],
        "exported_harmonic_sublattice_in_qsharp": [
            [int(value) for value in row]
            for row in exported_harmonic_in_qsharp.rows()],
        "qsharp_shortest_coordinates": [
            int(value) for value in shortest_coordinates],
        "qsharp_shortest_squared_norm": str(shortest_squared_norm),
        "qsharp_shortest_norm_approx": float(shortest_squared_norm.sqrt()),
        "qsharp_shortest_is_integral_harmonic": shortest_is_integral_harmonic,
        "qsharp_shortest_discriminant_class_order": shortest_class_order,
        "spherical_template_max_squared_norm": str(
            spherical_template_max_squared_norm),
        "qsharp_shortest_below_spherical_threshold": bool(
            shortest_squared_norm * spherical_template_max_squared_norm < 1),
        "threshold_product_squared": str(
            shortest_squared_norm * spherical_template_max_squared_norm),
        "screen_conclusion": (
            "safe_all_nonzero_qsharp_vectors_above_threshold"
            if shortest_squared_norm * spherical_template_max_squared_norm >= 1
            else (
                "dangerous_nonintegral_class_below_threshold"
                if not shortest_is_integral_harmonic
                else "inconclusive_shortest_vector_is_integral_harmonic")),
    }
    rendered = json.dumps(certificate, indent=2, sort_keys=True) + "\n"
    args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
