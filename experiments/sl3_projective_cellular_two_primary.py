"""Audit the orientation-torsion sector of projective cellular charts.

The rational signed-coinvariant complex discards every orbit on which a
stabilizer reverses orientation.  Integrally such an orbit contributes a
``Z/2`` coordinate.  Modulo two all signs disappear, so the full unsigned
orbit complex is an exact finite shadow of the omitted sector.  This
MSI-only script records both orbit decompositions, constructs the unsigned
``F_2`` boundary complex, and verifies its homology exactly.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from sage.all import GF, matrix

from sl3_projective_cellular_analyze import SignedDSU, build_boundaries, parse


def orbit_data(degree, cell, retain_bad):
    dsu = SignedDSU(degree)
    for sign, permutation in cell.stabilizers:
        if retain_bad:
            sign = 1
        for source, target in enumerate(permutation):
            dsu.union(source, target, sign)
    roots = {}
    coordinates = []
    for point in range(degree):
        root, sign = dsu.find(point)
        root, _ = dsu.find(root)
        if not retain_bad and dsu.bad[root]:
            coordinates.append(None)
            continue
        if root not in roots:
            roots[root] = len(roots)
        coordinates.append((roots[root], 1 if retain_bad else sign))
    bad_roots = set()
    if retain_bad:
        signed = SignedDSU(degree)
        for sign, permutation in cell.stabilizers:
            for source, target in enumerate(permutation):
                signed.union(source, target, sign)
        for point in range(degree):
            root, _ = signed.find(point)
            root, _ = signed.find(root)
            if signed.bad[root]:
                bad_roots.add(root)
    return len(roots), coordinates, len(bad_roots)


def build_mod_two_complex(degree, orbit_dimensions, cells):
    field = GF(2)
    offsets = []
    coordinate_maps = {}
    dimensions = []
    torsion_counts = []
    cell_counts = []
    for q, count in enumerate(orbit_dimensions):
        q_offsets = {}
        total = 0
        torsion = 0
        q_cell_counts = []
        for cell_index in range(1, count + 1):
            dimension, coordinate_map, bad = orbit_data(
                degree, cells[(q, cell_index)], retain_bad=True)
            q_offsets[cell_index] = total
            coordinate_maps[(q, cell_index)] = coordinate_map
            total += dimension
            torsion += bad
            q_cell_counts.append({
                "unsigned_orbits": dimension,
                "orientation_torsion_orbits": bad,
            })
        offsets.append(q_offsets)
        dimensions.append(total)
        torsion_counts.append(torsion)
        cell_counts.append(q_cell_counts)

    boundaries = {}
    for q in range(1, len(orbit_dimensions)):
        entries = {}
        for cell_index in range(1, orbit_dimensions[q] + 1):
            source_map = coordinate_maps[(q, cell_index)]
            representatives = {}
            for point, value in enumerate(source_map):
                if value[0] not in representatives:
                    representatives[value[0]] = point
            for local_source, point in representatives.items():
                source = offsets[q][cell_index] + local_source
                for signed_target, permutation in cells[(q, cell_index)].boundaries:
                    target_cell = abs(signed_target)
                    local_target, _ = coordinate_maps[
                        (q - 1, target_cell)][permutation[point]]
                    target = offsets[q - 1][target_cell] + local_target
                    entries[(source, target)] = (
                        entries.get((source, target), 0) + 1) % 2
        boundaries[q] = matrix(
            field,
            dimensions[q],
            dimensions[q - 1],
            {(row, column): value
             for (row, column), value in entries.items() if value},
            sparse=True,
        )
    return dimensions, torsion_counts, cell_counts, boundaries


def analyze(path):
    prime, degree, orbit_dimensions, cells = parse(path)
    rational_dimensions, rational_boundaries = build_boundaries(
        degree, orbit_dimensions, cells)
    dimensions, torsion_counts, cell_counts, boundaries = build_mod_two_complex(
        degree, orbit_dimensions, cells)
    square_zero = {}
    for q in range(2, len(orbit_dimensions)):
        square_zero[str(q)] = (boundaries[q] * boundaries[q - 1]).is_zero()
        if not square_zero[str(q)]:
            raise AssertionError("mod-two boundary does not square to zero")
    ranks = {str(q): int(boundary.rank()) for q, boundary in boundaries.items()}
    homology = {
        str(q): dimensions[q] - ranks.get(str(q), 0) - ranks.get(str(q + 1), 0)
        for q in range(len(orbit_dimensions))
    }
    return {
        "prime": prime,
        "projective_degree": degree,
        "rational_free_dimensions": rational_dimensions,
        "orientation_torsion_C2_coordinate_counts": torsion_counts,
        "unsigned_mod_two_dimensions": dimensions,
        "cell_orbit_counts": cell_counts,
        "mod_two_boundary_ranks": ranks,
        "mod_two_homology_dimensions": homology,
        "mod_two_boundary_squared_zero": square_zero,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("inputs", type=Path, nargs="+")
    args = parser.parse_args()
    result = [analyze(path) for path in args.inputs]
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
