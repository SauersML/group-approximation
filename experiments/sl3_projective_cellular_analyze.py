"""Build and certify the rational projective cellular Shapiro complex.

The GAP exporter records the permutation action of every finite cell
stabilizer and every cellular boundary term.  This program takes signed
coinvariants exactly, builds sparse rational boundary matrices, checks
``d^2=0``, and computes rational homology dimensions.

Run with Sage's Python on MSI, not with a local Python interpreter.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path

from sage.all import QQ, RealField, ZZ, identity_matrix, lcm, matrix, vector


class SignedDSU:
    """Disjoint-set union with relations e_x = sign * e_y."""

    def __init__(self, size: int) -> None:
        self.parent = list(range(size))
        self.parity = [1] * size
        self.bad = [False] * size

    def find(self, item: int) -> tuple[int, int]:
        parent = self.parent[item]
        if parent == item:
            return item, 1
        root, sign = self.find(parent)
        self.parity[item] *= sign
        self.parent[item] = root
        return root, self.parity[item]

    def union(self, left: int, right: int, sign: int) -> None:
        left_root, left_sign = self.find(left)
        right_root, right_sign = self.find(right)
        if left_root == right_root:
            if left_sign != sign * right_sign:
                self.bad[left_root] = True
            return
        relation = left_sign * sign * right_sign
        self.parent[right_root] = left_root
        self.parity[right_root] = relation
        self.bad[left_root] = self.bad[left_root] or self.bad[right_root]


@dataclass
class Cell:
    stabilizers: list[tuple[int, list[int]]]
    boundaries: list[tuple[int, list[int]]]


def parse(path: Path):
    cells: dict[tuple[int, int], Cell] = {}
    with path.open() as stream:
        meta = stream.readline().split()
        if meta[0] != "META":
            raise ValueError("missing META header")
        prime = int(meta[1])
        degree = int(meta[2])
        orbit_dimensions = [int(value) for value in meta[3].split(",")]
        for line in stream:
            fields = line.split()
            kind = fields[0]
            q, r = int(fields[1]), int(fields[2])
            key = (q, r)
            if kind == "CELL":
                if key in cells:
                    raise ValueError(f"duplicate cell {key}")
                cells[key] = Cell([], [])
                continue
            sign_or_target = int(fields[3])
            permutation = [int(value) - 1 for value in fields[4].split(",")]
            if len(permutation) != degree or sorted(permutation) != list(range(degree)):
                raise ValueError(f"invalid permutation on {key}")
            if kind == "STAB":
                if sign_or_target not in (-1, 1):
                    raise ValueError("invalid orientation sign")
                cells[key].stabilizers.append((sign_or_target, permutation))
            elif kind == "BOUND":
                cells[key].boundaries.append((sign_or_target, permutation))
            else:
                raise ValueError(f"unknown record {kind}")
    return prime, degree, orbit_dimensions, cells


def coinvariants(degree: int, cell: Cell):
    dsu = SignedDSU(degree)
    for sign, permutation in cell.stabilizers:
        for source, target in enumerate(permutation):
            dsu.union(source, target, sign)
    roots = {}
    coordinates = []
    for point in range(degree):
        root, sign = dsu.find(point)
        root, _ = dsu.find(root)
        if dsu.bad[root]:
            coordinates.append(None)
            continue
        if root not in roots:
            roots[root] = len(roots)
        coordinates.append((roots[root], sign))
    return len(roots), coordinates


def build_boundaries(degree, orbit_dimensions, cells):
    offsets = []
    coordinate_maps = {}
    dimensions = []
    for q, count in enumerate(orbit_dimensions):
        q_offsets = {}
        total = 0
        for r in range(1, count + 1):
            dimension, coordinate_map = coinvariants(degree, cells[(q, r)])
            q_offsets[r] = total
            coordinate_maps[(q, r)] = coordinate_map
            total += dimension
        offsets.append(q_offsets)
        dimensions.append(total)

    boundaries = {}
    for q in range(1, len(orbit_dimensions)):
        entries = {}
        for r in range(1, orbit_dimensions[q] + 1):
            source_map = coordinate_maps[(q, r)]
            representatives = {}
            for point, value in enumerate(source_map):
                if value is not None and value[0] not in representatives:
                    representatives[value[0]] = (point, value[1])
            for local_source, (point, source_sign) in representatives.items():
                source = offsets[q][r] + local_source
                for signed_target, permutation in cells[(q, r)].boundaries:
                    target_cell = abs(signed_target)
                    target_value = coordinate_maps[(q - 1, target_cell)][permutation[point]]
                    if target_value is None:
                        continue
                    local_target, target_sign = target_value
                    target = offsets[q - 1][target_cell] + local_target
                    coefficient = (
                        (1 if signed_target > 0 else -1)
                        * target_sign
                        * source_sign
                    )
                    entries[(source, target)] = entries.get((source, target), 0) + coefficient
        boundaries[q] = matrix(
            QQ, dimensions[q], dimensions[q - 1],
            {(row, column): value for (row, column), value in entries.items() if value},
            sparse=True,
        )
    return dimensions, boundaries


def gauss_reduce_gram(gram):
    """Return an integral basis change and a Gauss-reduced Gram matrix of rank at most two."""
    if gram.nrows() != gram.ncols():
        raise ValueError("Gram matrix must be square")
    if gram.nrows() == 0:
        return identity_matrix(ZZ, 0), gram
    if gram.nrows() == 1:
        return identity_matrix(ZZ, 1), gram
    if gram.nrows() != 2:
        raise ValueError("Gauss reduction only handles Gram matrices of rank at most two")
    reduced = gram
    transform = identity_matrix(ZZ, 2)
    while True:
        if reduced[1, 1] < reduced[0, 0]:
            change = matrix(ZZ, [[0, 1], [1, 0]])
            reduced = change * reduced * change.transpose()
            transform = change * transform
            continue
        quotient = ZZ((reduced[0, 1] / reduced[0, 0]).round())
        if quotient:
            change = matrix(ZZ, [[1, 0], [-quotient, 1]])
            reduced = change * reduced * change.transpose()
            transform = change * transform
            continue
        if 2 * abs(reduced[0, 1]) <= reduced[0, 0]:
            break
        raise AssertionError("binary Gauss reduction did not make progress")
    if abs(transform.det()) != 1 or reduced != transform * gram * transform.transpose():
        raise AssertionError("invalid binary Gram reduction")
    return transform, reduced


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--harmonic-output", type=Path)
    parser.add_argument("--lift-output", type=Path)
    args = parser.parse_args()

    prime, degree, orbit_dimensions, cells = parse(args.input)
    dimensions, boundaries = build_boundaries(degree, orbit_dimensions, cells)
    square_zero = {}
    for q in range(2, len(orbit_dimensions)):
        product = boundaries[q] * boundaries[q - 1]
        square_zero[str(q)] = product.is_zero()
        if not product.is_zero():
            raise AssertionError(f"cellular boundary does not square to zero in degree {q}")

    ranks = {str(q): int(boundary.rank()) for q, boundary in boundaries.items()}
    homology = {}
    for q in range(len(orbit_dimensions)):
        incoming = ranks.get(str(q + 1), 0)
        outgoing = ranks.get(str(q), 0)
        homology[str(q)] = dimensions[q] - incoming - outgoing

    harmonic_basis = matrix(ZZ, 0, dimensions[2])
    harmonic_hash = None
    if homology.get("2", 0):
        harmonic_system = boundaries[2].transpose().stack(boundaries[3])
        harmonic_basis = harmonic_system.change_ring(ZZ).right_kernel_matrix()
        harmonic_basis = matrix(ZZ, harmonic_basis, sparse=False).LLL()
        if harmonic_basis.nrows() != homology["2"]:
            raise AssertionError("harmonic kernel dimension differs from H_2")
        if harmonic_system * harmonic_basis.transpose() != 0:
            raise AssertionError("integral harmonic basis has nonzero residual")
        if args.harmonic_output:
            digest = hashlib.sha256()
            with args.harmonic_output.open("w", encoding="ascii") as stream:
                header = "coordinate " + " ".join(
                    f"basis_{index}" for index in range(harmonic_basis.nrows())) + "\n"
                stream.write(header)
                digest.update(header.encode("ascii"))
                for column in range(harmonic_basis.ncols()):
                    line = str(column) + " " + " ".join(
                        str(harmonic_basis[row, column])
                        for row in range(harmonic_basis.nrows())) + "\n"
                    stream.write(line)
                    digest.update(line.encode("ascii"))
            harmonic_hash = digest.hexdigest()

    harmonic_gram = harmonic_basis * harmonic_basis.transpose()
    spherical_template_max_squared_norm = max(
        sum(value * value for value in boundaries[3].row(row))
        for row in range(boundaries[3].nrows()))

    lift_data = None
    if args.lift_output and harmonic_basis.nrows():
        d2_integer = boundaries[2].change_ring(ZZ)
        print("lift: computing the primitive cellular cycle lattice", flush=True)
        cycle_basis = d2_integer.transpose().right_kernel_matrix()
        if cycle_basis.nrows() != dimensions[2] - ranks["2"]:
            raise AssertionError("cycle lattice has the wrong rank")
        print("lift: recovering Q-sharp from its integral pairings", flush=True)
        harmonic_cycle_pairing = harmonic_basis * cycle_basis.transpose()
        pairing_lattice = harmonic_cycle_pairing.transpose().row_module()
        pairing_basis = pairing_lattice.basis_matrix()
        if pairing_basis.nrows() != harmonic_basis.nrows():
            raise AssertionError("harmonic pairing lattice has the wrong rank")
        qsharp_coordinates = pairing_basis.transpose().inverse()
        qsharp_basis = qsharp_coordinates * harmonic_basis
        if any(value.denominator() != 1
               for value in (qsharp_basis * cycle_basis.transpose()).list()):
            raise AssertionError("Q-sharp basis has a nonintegral cycle pairing")
        qsharp_gram = qsharp_basis * qsharp_basis.transpose()
        harmonic_in_qsharp = qsharp_coordinates.inverse()
        if any(value.denominator() != 1 for value in harmonic_in_qsharp.list()):
            raise AssertionError("harmonic lattice has nonintegral Q-sharp coordinates")
        harmonic_in_qsharp = harmonic_in_qsharp.change_ring(ZZ)
        harmonic_smith = harmonic_in_qsharp.smith_form()[0]
        harmonic_discriminant = [
            abs(int(harmonic_smith[index, index]))
            for index in range(harmonic_smith.nrows())
            if harmonic_smith[index, index]
        ]
        qsharp_reduction, qsharp_reduced_gram = gauss_reduce_gram(qsharp_gram)
        shortest_coordinates = vector(ZZ, qsharp_reduction.row(0))
        harmonic_coordinate_lattice = harmonic_in_qsharp.row_module()
        shortest_is_integral_harmonic = shortest_coordinates in harmonic_coordinate_lattice
        quotient_coordinates = (
            shortest_coordinates * harmonic_in_qsharp.change_ring(QQ).inverse())
        shortest_class_order = int(lcm([
            value.denominator() for value in quotient_coordinates
        ]))
        print("lift: constructing an integral right inverse for cycle pairings", flush=True)
        cycle_hnf, cycle_transform = cycle_basis.transpose().hermite_form(
            transformation=True, include_zero_rows=True)
        cycle_rank = cycle_basis.nrows()
        if cycle_hnf[:cycle_rank, :] != identity_matrix(ZZ, cycle_rank):
            raise AssertionError("primitive cycle lattice did not give unit column HNF")
        if cycle_hnf[cycle_rank:, :] != 0:
            raise AssertionError("cycle column HNF has a nonzero tail")
        cycle_pairing_right_inverse = cycle_transform.transpose()[:, :cycle_rank]
        if cycle_basis * cycle_pairing_right_inverse != identity_matrix(ZZ, cycle_rank):
            raise AssertionError("invalid integral right inverse for cycle pairings")
        qsharp_cycle_pairing = qsharp_basis * cycle_basis.transpose()
        qsharp_cycle_pairing = qsharp_cycle_pairing.change_ring(ZZ)
        lift_basis = (
            cycle_pairing_right_inverse * qsharp_cycle_pairing.transpose()
        ).transpose()
        if boundaries[3].change_ring(ZZ) * lift_basis.transpose() != 0:
            raise AssertionError("integral Q-sharp lifts do not annihilate boundaries")
        if lift_basis * cycle_basis.transpose() != qsharp_cycle_pairing:
            raise AssertionError("integral lifts have the wrong harmonic projection")
        raw_lift_basis = lift_basis
        print("lift: reducing the section in an integral range parallelepiped", flush=True)
        range_generators = d2_integer.transpose()
        range_pivots = range_generators.transpose().change_ring(QQ).pivots()
        range_basis = range_generators.matrix_from_rows(range_pivots)
        rational_range = range_basis.change_ring(QQ).row_space()
        reduced_lifts = []
        for index, lift in enumerate(lift_basis.rows()):
            range_component = lift.change_ring(QQ) - qsharp_basis.row(index)
            coordinates = rational_range.coordinate_vector(range_component)
            integral_coordinates = vector(ZZ, [value.round() for value in coordinates])
            reduced_lifts.append(lift - integral_coordinates * range_basis)
        parallelepiped_lifts = matrix(ZZ, reduced_lifts)
        if boundaries[3].change_ring(ZZ) * parallelepiped_lifts.transpose() != 0:
            raise AssertionError("reduced lifts do not annihilate boundaries")
        if parallelepiped_lifts * cycle_basis.transpose() != qsharp_cycle_pairing:
            raise AssertionError("range reduction changed the harmonic projection")

        variable = QQ["lambda"].gen()
        real_field = RealField(256)

        def section_metric(candidate):
            candidate_gram = candidate * candidate.transpose()
            polynomial = (candidate_gram - variable * qsharp_gram).det()
            generalized = qsharp_gram.inverse() * candidate_gram
            trace = generalized.trace()
            determinant = generalized.det()
            discriminant = trace * trace - 4 * determinant
            if discriminant < 0:
                raise AssertionError("generalized section spectrum is not real")
            root_discriminant = real_field(discriminant).sqrt()
            roots = sorted([
                float((real_field(trace) - root_discriminant) / 2),
                float((real_field(trace) + root_discriminant) / 2),
            ])
            return roots[-1], candidate_gram, polynomial, roots

        raw_metric = section_metric(raw_lift_basis)
        parallelepiped_metric = section_metric(parallelepiped_lifts)
        if parallelepiped_metric[0] < raw_metric[0]:
            lift_basis = parallelepiped_lifts
            selected_metric = parallelepiped_metric
            section_choice = "range_parallelepiped"
        else:
            lift_basis = raw_lift_basis
            selected_metric = raw_metric
            section_choice = "cycle_hnf_right_inverse"
        _, lift_gram, section_polynomial, section_roots = selected_metric

        shortest_qsharp = shortest_coordinates * qsharp_basis
        shortest_lift = shortest_coordinates * lift_basis
        shortest_range_component = shortest_lift.change_ring(QQ) - shortest_qsharp
        shortest_range_coordinates = rational_range.coordinate_vector(
            shortest_range_component)
        shortest_range_integral_coordinates = vector(ZZ, [
            value.round() for value in shortest_range_coordinates
        ])
        shortest_lift = (
            shortest_lift - shortest_range_integral_coordinates * range_basis)
        shortest_range_component = shortest_lift.change_ring(QQ) - shortest_qsharp
        shortest_range_radius_upper_squared = shortest_range_component.dot_product(
            shortest_range_component)
        shortest_lift_squared_norm = shortest_lift.dot_product(shortest_lift)
        shortest_paired_distortion_upper_squared = (
            shortest_lift_squared_norm / qsharp_reduced_gram[0, 0])
        if boundaries[3].change_ring(ZZ) * shortest_lift.column() != 0:
            raise AssertionError("shortest-class lift does not annihilate boundaries")
        digest = hashlib.sha256()
        with args.lift_output.open("w", encoding="ascii") as stream:
            header = "coordinate " + " ".join(
                f"qsharp_{index}" for index in range(qsharp_basis.nrows())) + " " + " ".join(
                f"lift_{index}" for index in range(lift_basis.nrows())) + "\n"
            stream.write(header)
            digest.update(header.encode("ascii"))
            for column in range(qsharp_basis.ncols()):
                line = str(column) + " " + " ".join(
                    str(qsharp_basis[row, column])
                    for row in range(qsharp_basis.nrows())) + " " + " ".join(
                    str(lift_basis[row, column])
                    for row in range(lift_basis.nrows())) + "\n"
                stream.write(line)
                digest.update(line.encode("ascii"))
        lift_data = {
            "cycle_lattice_rank": int(cycle_basis.nrows()),
            "pairing_lattice_basis": [
                [int(value) for value in row] for row in pairing_basis.rows()],
            "qsharp_and_lift_basis_sha256": digest.hexdigest(),
            "qsharp_maximum_numerator": max(
                abs(int(value.numerator())) for value in qsharp_basis.list()),
            "qsharp_common_denominator": int(qsharp_basis.denominator()),
            "qsharp_support_sizes": [
                int(sum(1 for value in qsharp_basis.row(row) if value))
                for row in range(qsharp_basis.nrows())],
            "qsharp_gram": [[str(value) for value in row] for row in qsharp_gram.rows()],
            "harmonic_in_qsharp": [
                [int(value) for value in row] for row in harmonic_in_qsharp.rows()],
            "harmonic_discriminant_invariants": harmonic_discriminant,
            "qsharp_gauss_transform": [
                [int(value) for value in row] for row in qsharp_reduction.rows()],
            "qsharp_gauss_reduced_gram": [
                [str(value) for value in row] for row in qsharp_reduced_gram.rows()],
            "qsharp_shortest_squared_norm": str(qsharp_reduced_gram[0, 0]),
            "qsharp_shortest_norm_approx": float(qsharp_reduced_gram[0, 0].sqrt()),
            "qsharp_shortest_is_integral_harmonic": shortest_is_integral_harmonic,
            "qsharp_shortest_discriminant_class_order": shortest_class_order,
            "qsharp_shortest_below_spherical_threshold": (
                qsharp_reduced_gram[0, 0] * spherical_template_max_squared_norm < 1),
            "integral_lift_maximum_absolute_coefficient": max(
                abs(int(value)) for value in lift_basis.list()),
            "integral_lift_support_sizes": [
                int(sum(1 for value in lift_basis.row(row) if value))
                for row in range(lift_basis.nrows())],
            "integral_lift_gram": [
                [int(value) for value in row] for row in lift_gram.rows()],
            "integral_section_squared_norm_polynomial": str(section_polynomial),
            "integral_section_squared_norm_roots": section_roots,
            "integral_section_norm": section_roots[-1] ** 0.5,
            "integral_section_choice": section_choice,
            "range_parallelepiped_section_norm": parallelepiped_metric[0] ** 0.5,
            "shortest_class_lift_squared_norm": str(shortest_lift_squared_norm),
            "shortest_class_range_radius_upper_squared": str(
                shortest_range_radius_upper_squared),
            "shortest_class_paired_distortion_upper_squared": str(
                shortest_paired_distortion_upper_squared),
            "shortest_class_paired_distortion_upper": float(
                shortest_paired_distortion_upper_squared.sqrt()),
        }

    result = {
        "prime": prime,
        "projective_degree": degree,
        "cell_orbit_dimensions": orbit_dimensions,
        "rational_coinvariant_dimensions": dimensions,
        "boundary_ranks": ranks,
        "homology_dimensions": homology,
        "boundary_squared_zero": square_zero,
        "integral_harmonic_rank": int(harmonic_basis.nrows()),
        "integral_harmonic_maximum_absolute_coefficient": (
            max(abs(int(value)) for value in harmonic_basis.list())
            if harmonic_basis.nrows() else 0),
        "integral_harmonic_support_sizes": [
            int(sum(1 for value in harmonic_basis.row(row) if value))
            for row in range(harmonic_basis.nrows())],
        "integral_harmonic_gram": [
            [int(harmonic_gram[row, column])
             for column in range(harmonic_gram.ncols())]
            for row in range(harmonic_gram.nrows())],
        "integral_harmonic_basis_sha256": harmonic_hash,
        "spherical_template_max_squared_norm": str(
            spherical_template_max_squared_norm),
        "harmonic_lift_sequence": lift_data,
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
