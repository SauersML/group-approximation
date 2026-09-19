"""Certify the harmonic index and section metric of an exact cycle packet.

The harmonic TSV supplies an integral basis ``H`` of the rational harmonic
space.  The systole certificate supplies a basis ``B`` of the pairing lattice
``H Z_2``.  Hence ``(B^T)^(-1) H`` is a basis of ``Q^#``.  Pairing it with a
square packet of integral cycles gives an integral matrix ``M`` whose absolute
determinant is exactly the index of the projected packet in the primal lattice
``Q``.

The script also computes the exact Gram matrix of the harmonic projections and
the characteristic polynomial of the generalized section metric

    det(G_ambient - t G_harmonic).

It does not claim that the chosen representatives minimize their boundary
cosets; it certifies the section that the input packet actually defines.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from sage.all import QQ, RealField, ZZ, matrix, vector


def read_harmonic_basis(path: Path):
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
            for row, value in enumerate(fields[1:]):
                rows[row].append(int(value))
    return matrix(ZZ, rows), digest


def rational_matrix_json(value):
    return [[str(entry) for entry in row] for row in value.rows()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("packet", type=Path)
    parser.add_argument("harmonic_basis", type=Path)
    parser.add_argument("systole_certificate", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--primal-packet", type=Path)
    parser.add_argument("--transformed-packet-output", type=Path)
    args = parser.parse_args()

    packet_bytes = args.packet.read_bytes()
    packet = json.loads(packet_bytes)
    systole_bytes = args.systole_certificate.read_bytes()
    systole = json.loads(systole_bytes)
    harmonic_basis, harmonic_hash = read_harmonic_basis(args.harmonic_basis)

    if packet["level"] != systole["level"]:
        raise ValueError("packet and systole levels differ")
    if harmonic_hash != systole["harmonic_basis_sha256"]:
        raise ValueError("harmonic basis hash differs from systole certificate")
    selected = packet["shortest_spanning_packet_indices"]
    rank = harmonic_basis.nrows()
    if len(selected) != rank:
        raise ValueError("selected packet is not square")

    ambient_dimension = harmonic_basis.ncols()
    cycles = []
    for index in selected:
        cycle = vector(ZZ, ambient_dimension)
        for entry in packet["records"][index]["representative"]:
            cycle[entry["coordinate"]] = entry["coefficient"]
        cycles.append(cycle)
    cycle_matrix = matrix(ZZ, cycles)

    pairing_basis = matrix(ZZ, systole["pairing_lattice_basis"])
    if pairing_basis.nrows() != rank or pairing_basis.ncols() != rank:
        raise ValueError("pairing lattice basis has the wrong shape")
    qsharp_coordinates = pairing_basis.transpose().inverse()
    harmonic_cycle_pairings = harmonic_basis * cycle_matrix.transpose()
    integral_pairings = qsharp_coordinates * harmonic_cycle_pairings
    if any(entry.denominator() != 1 for entry in integral_pairings.list()):
        raise AssertionError("Q-sharp has a nonintegral packet pairing")
    integral_pairings = integral_pairings.change_ring(ZZ)
    projected_packet_index = abs(int(integral_pairings.det()))
    if not projected_packet_index:
        raise AssertionError("packet projections are rationally dependent")

    harmonic_gram_basis = harmonic_basis * harmonic_basis.transpose()
    projected_gram = (
        harmonic_cycle_pairings.transpose()
        * harmonic_gram_basis.inverse()
        * harmonic_cycle_pairings)
    ambient_gram = cycle_matrix * cycle_matrix.transpose()
    if projected_gram != projected_gram.transpose():
        raise AssertionError("projected Gram matrix is not symmetric")
    if not projected_gram.is_positive_definite():
        raise AssertionError("projected Gram matrix is not positive definite")

    variable = QQ["t"].gen()
    section_polynomial = (ambient_gram - variable * projected_gram).det()
    normalized_section_polynomial = section_polynomial / section_polynomial[rank]
    real_field = RealField(100)
    roots = sorted(
        real_field(root[0])
        for root in normalized_section_polynomial.roots(real_field))
    if len(roots) != rank:
        raise AssertionError("generalized section polynomial is not real split")
    maximum_section_distortion_squared = roots[-1]

    transformed_packet_data = None
    if args.primal_packet is not None:
        if args.transformed_packet_output is None:
            raise ValueError(
                "--primal-packet requires --transformed-packet-output")
        primal_bytes = args.primal_packet.read_bytes()
        primal = json.loads(primal_bytes)
        if primal["level"] != packet["level"]:
            raise ValueError("primal packet and cycle packet levels differ")
        basis_change = matrix(ZZ, primal["primal_packet_basis_change"])
        cycle_basis_change = (
            basis_change * integral_pairings.transpose().inverse())
        if any(entry.denominator() != 1
               for entry in cycle_basis_change.list()):
            raise AssertionError(
                "short primal basis does not lift integrally through packet")
        cycle_basis_change = cycle_basis_change.change_ring(ZZ)
        if abs(cycle_basis_change.det()) != 1:
            raise AssertionError("cycle packet basis change is not unimodular")
        transformed_cycles = cycle_basis_change * cycle_matrix
        transformed_harmonic_gram = (
            cycle_basis_change * projected_gram
            * cycle_basis_change.transpose())
        certified_primal_gram = matrix(QQ, [
            [QQ(entry) for entry in row]
            for row in primal["primal_packet_gram"]])
        if transformed_harmonic_gram != certified_primal_gram:
            raise AssertionError(
                "transported harmonic Gram differs from primal certificate")
        transformed_packet_data = {
            "level": packet["level"],
            "source_packet_sha256": hashlib.sha256(packet_bytes).hexdigest(),
            "source_primal_packet_sha256": hashlib.sha256(primal_bytes).hexdigest(),
            "cycle_basis_change": [
                [int(entry) for entry in row]
                for row in cycle_basis_change.rows()],
            "exact_short_homology_circuits": [
                {
                    "kernel_row": f"primal_packet_{row}",
                    "coordinates": [
                        {"coordinate": int(column), "coefficient": int(value)}
                        for column, value in enumerate(transformed_cycles.row(row))
                        if value],
                }
                for row in range(rank)],
            "scope": (
                "unimodular transport of the exact integral cycle packet to "
                "the certified short primal harmonic basis; representatives "
                "have not yet been reduced by cellular boundaries"),
        }
        args.transformed_packet_output.write_text(
            json.dumps(transformed_packet_data, indent=2, sort_keys=True) + "\n",
            encoding="utf-8")

    certificate = {
        "level": packet["level"],
        "packet_sha256": hashlib.sha256(packet_bytes).hexdigest(),
        "systole_certificate_sha256": hashlib.sha256(systole_bytes).hexdigest(),
        "harmonic_basis_sha256": harmonic_hash,
        "harmonic_rank": rank,
        "selected_packet_indices": selected,
        "qsharp_packet_pairing_matrix": [
            [int(entry) for entry in row]
            for row in integral_pairings.rows()],
        "projected_packet_index_in_q": projected_packet_index,
        "projected_packet_is_q_basis": projected_packet_index == 1,
        "ambient_packet_gram": [
            [int(entry) for entry in row] for row in ambient_gram.rows()],
        "projected_harmonic_packet_gram": rational_matrix_json(projected_gram),
        "generalized_section_polynomial_monic": str(
            normalized_section_polynomial),
        "generalized_section_roots_approx": [str(root) for root in roots],
        "maximum_section_distortion_squared_approx": str(
            maximum_section_distortion_squared),
        "maximum_section_distortion_approx": str(
            maximum_section_distortion_squared.sqrt()),
        "scope": (
            "exact index and exact generalized section polynomial for the "
            "displayed packet; representatives are certified upper bounds, "
            "not boundary-coset CVP optima"),
    }
    if transformed_packet_data is not None:
        certificate.update({
            "primal_packet_sha256": hashlib.sha256(primal_bytes).hexdigest(),
            "transformed_cycle_basis_change": (
                transformed_packet_data["cycle_basis_change"]),
            "transformed_packet_sha256": hashlib.sha256(
                args.transformed_packet_output.read_bytes()).hexdigest(),
        })
    args.output.write_text(
        json.dumps(certificate, indent=2, sort_keys=True) + "\n",
        encoding="utf-8")
    print(json.dumps({
        "level": packet["level"],
        "projected_packet_index_in_q": projected_packet_index,
        "maximum_section_distortion_squared_approx": str(
            maximum_section_distortion_squared),
        "maximum_section_distortion_approx": str(
            maximum_section_distortion_squared.sqrt()),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
