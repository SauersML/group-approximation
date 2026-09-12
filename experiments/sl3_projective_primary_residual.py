"""Measure the residual orientation-primary boundary in projective charts.

The first degree-two orientation-torsion block cancels the degree-one block
uniformly.  This MSI-only experiment extracts the remaining mod-two map from
the degree-three torsion coordinates to the second degree-two cell's torsion
coordinates.  It records exact rank and Tanner-incidence data; it does not
replace the higher stabilizer-resolution rows of the derived complex.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from sage.all import GF, matrix

from sl3_projective_cellular_analyze import SignedDSU, parse


def signed_orbits(degree, cell):
    dsu = SignedDSU(degree)
    for sign, permutation in cell.stabilizers:
        for source, target in enumerate(permutation):
            dsu.union(source, target, sign)

    roots = {}
    representatives = {}
    for point in range(degree):
        root, _ = dsu.find(point)
        root, _ = dsu.find(root)
        if root not in roots:
            roots[root] = len(roots)
            representatives[root] = point

    torsion_roots = [root for root in roots if dsu.bad[root]]
    torsion_index = {root: index for index, root in enumerate(torsion_roots)}
    point_to_torsion = []
    for point in range(degree):
        root, _ = dsu.find(point)
        root, _ = dsu.find(root)
        point_to_torsion.append(torsion_index.get(root))
    torsion_representatives = [representatives[root] for root in torsion_roots]
    return point_to_torsion, torsion_representatives


def residual_boundary(path: Path):
    prime, degree, orbit_dimensions, cells = parse(path)
    if orbit_dimensions[2] != 2 or orbit_dimensions[3] != 1:
        raise ValueError("expected two degree-two cells and one degree-three cell")

    source_map, source_representatives = signed_orbits(degree, cells[(3, 1)])
    target_map, target_representatives = signed_orbits(degree, cells[(2, 2)])
    del source_map

    entries = {}
    raw_target_hits = [0] * len(target_representatives)
    boundary_terms = [
        permutation
        for signed_target, permutation in cells[(3, 1)].boundaries
        if abs(signed_target) == 2
    ]
    for source, point in enumerate(source_representatives):
        for permutation in boundary_terms:
            target = target_map[permutation[point]]
            if target is None:
                continue
            raw_target_hits[target] += 1
            entries[(source, target)] = (entries.get((source, target), 0) + 1) % 2

    residual = matrix(
        GF(2),
        len(source_representatives),
        len(target_representatives),
        {(row, column): value
         for (row, column), value in entries.items() if value},
        sparse=True,
    )
    row_weights = [len(residual.row(index).dict()) for index in range(residual.nrows())]
    column_weights = [
        len(residual.column(index).dict()) for index in range(residual.ncols())
    ]
    rank = int(residual.rank())
    return {
        "prime": prime,
        "projective_degree": degree,
        "boundary_terms_to_second_degree_two_cell": len(boundary_terms),
        "source_degree_three_C2_coordinates": residual.nrows(),
        "target_second_degree_two_C2_coordinates": residual.ncols(),
        "rank_over_F2": rank,
        "kernel_dimension": residual.nrows() - rank,
        "cokernel_dimension": residual.ncols() - rank,
        "row_weight_histogram": {
            str(weight): row_weights.count(weight) for weight in sorted(set(row_weights))
        },
        "column_weight_histogram": {
            str(weight): column_weights.count(weight)
            for weight in sorted(set(column_weights))
        },
        "raw_target_hit_histogram": {
            str(weight): raw_target_hits.count(weight)
            for weight in sorted(set(raw_target_hits))
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("inputs", type=Path, nargs="+")
    args = parser.parse_args()
    result = [residual_boundary(path) for path in args.inputs]
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    columns = (
        "prime",
        "projective_degree",
        "source_degree_three_C2_coordinates",
        "target_second_degree_two_C2_coordinates",
        "rank_over_F2",
        "kernel_dimension",
        "cokernel_dimension",
        "zero_rows",
        "weight_two_rows",
        "zero_columns",
        "weight_one_columns",
    )
    lines = ["\t".join(columns)]
    for row in result:
        values = {
            **row,
            "zero_rows": row["row_weight_histogram"].get("0", 0),
            "weight_two_rows": row["row_weight_histogram"].get("2", 0),
            "zero_columns": row["column_weight_histogram"].get("0", 0),
            "weight_one_columns": row["column_weight_histogram"].get("1", 0),
        }
        lines.append("\t".join(str(values[column]) for column in columns))
    args.output.with_suffix(".tsv").write_text("\n".join(lines) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
