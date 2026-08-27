"""Compute the vertical E1 rows of the projective derived resolution.

Run on MSI after ``sl3_projective_h2_export.g``.  The HAP resolution retains
the Wall bidegree ``(q,s)``.  This script reduces the first three specialized
boundaries in characteristic two or three, extracts the vertical blocks
preserving ``q``, and computes the exact filtered homology data in total
degree two.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from sage.all import GF, matrix


Q_BY_TOTAL_GENERATOR = {
    0: [0],
    1: [0, 0, 0, 1],
    2: [0, 0, 0, 0, 0, 0, 1, 1, 2, 2],
    3: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3],
}


def read_boundary(path: Path, field):
    lines = path.read_text(encoding="utf-8").splitlines()
    source_rank, target_rank = map(int, lines[0].split())
    entries = {}
    for line in lines[1:]:
        source, target, coefficient = map(int, line.split())
        key = (source, target)
        entries[key] = entries.get(key, field.zero()) + field(coefficient)
    return matrix(
        field,
        source_rank,
        target_rank,
        {key: value for key, value in entries.items() if value},
        sparse=True,
    )


def coordinate_indices(total_degree: int, cellular_degree: int, degree: int):
    return [
        generator * degree + coordinate
        for generator, q in enumerate(Q_BY_TOTAL_GENERATOR[total_degree])
        if q == cellular_degree
        for coordinate in range(degree)
    ]


def vertical_rank(boundaries, total_degree: int, cellular_degree: int, degree: int):
    source = coordinate_indices(total_degree, cellular_degree, degree)
    target = coordinate_indices(total_degree - 1, cellular_degree, degree)
    block = boundaries[total_degree].matrix_from_rows_and_columns(source, target)
    return int(block.rank()), block.nrows(), block.ncols()


def filtered_block(
    boundaries, total_degree: int, source_q: int, target_q: int, degree: int
):
    source = coordinate_indices(total_degree, source_q, degree)
    target = coordinate_indices(total_degree - 1, target_q, degree)
    return boundaries[total_degree].matrix_from_rows_and_columns(source, target)


def horizontal_h1_rank(boundaries, degree: int):
    """Rank of E1_(1,1) -> E1_(0,1), modulo vertical boundaries."""

    source_vertical_out = filtered_block(boundaries, 2, 1, 1, degree)
    source_vertical_in = filtered_block(boundaries, 3, 1, 1, degree)
    target_vertical_out = filtered_block(boundaries, 1, 0, 0, degree)
    target_vertical_in = filtered_block(boundaries, 2, 0, 0, degree)
    horizontal = filtered_block(boundaries, 2, 1, 0, degree)

    source_cycles = source_vertical_out.left_kernel().basis_matrix()
    if source_vertical_in * source_vertical_out:
        raise AssertionError("source vertical boundaries are not cycles")
    images = source_cycles * horizontal
    if images * target_vertical_out:
        raise AssertionError("horizontal images are not target vertical cycles")

    induced_rank = int(target_vertical_in.stack(images).rank()) \
        - int(target_vertical_in.rank())
    source_h1 = source_vertical_out.nrows() \
        - int(source_vertical_out.rank()) - int(source_vertical_in.rank())
    target_h1 = target_vertical_out.nrows() \
        - int(target_vertical_out.rank()) - int(target_vertical_in.rank())
    return {
        "source_dimension": source_h1,
        "target_dimension": target_h1,
        "rank": induced_rank,
        "kernel_dimension": source_h1 - induced_rank,
        "cokernel_dimension": target_h1 - induced_rank,
    }


def horizontal_image_rank(
    boundaries, total_degree: int, source_q: int, target_q: int, degree: int
):
    """Rank on E1 without needing the next source vertical boundary."""

    source_vertical_out = filtered_block(
        boundaries, total_degree, source_q, source_q, degree)
    target_vertical_out = filtered_block(
        boundaries, total_degree - 1, target_q, target_q, degree)
    target_vertical_in = filtered_block(
        boundaries, total_degree, target_q, target_q, degree)
    horizontal = filtered_block(
        boundaries, total_degree, source_q, target_q, degree)

    source_cycles = source_vertical_out.left_kernel().basis_matrix()
    images = source_cycles * horizontal
    if images * target_vertical_out:
        raise AssertionError("horizontal images are not target vertical cycles")
    return int(target_vertical_in.stack(images).rank()) \
        - int(target_vertical_in.rank())


def higher_image_ranks(boundaries, degree: int):
    """Ranks of d2 and d3 into the surviving E2_(0,2) term."""

    high_target = coordinate_indices(2, 2, degree) \
        + coordinate_indices(2, 1, degree)
    low_target = coordinate_indices(2, 0, degree)

    def corrected_images(source_qs):
        source = sum(
            (coordinate_indices(3, q, degree) for q in source_qs), [])
        high = boundaries[3].matrix_from_rows_and_columns(source, high_target)
        low = boundaries[3].matrix_from_rows_and_columns(source, low_target)
        return high.left_kernel().basis_matrix() * low

    target_vertical_out = filtered_block(boundaries, 2, 0, 0, degree)
    target_vertical_in = filtered_block(boundaries, 3, 0, 0, degree)
    q1_vertical_out = filtered_block(boundaries, 3, 1, 1, degree)
    q1_horizontal = filtered_block(boundaries, 3, 1, 0, degree)
    q1_cycles = q1_vertical_out.left_kernel().basis_matrix()
    e1_boundaries = q1_cycles * q1_horizontal
    e2_denominator = target_vertical_in.stack(e1_boundaries)
    d2_images = corrected_images((2, 1))

    if e2_denominator * target_vertical_out:
        raise AssertionError("E2 target denominator is not made of cycles")
    if d2_images * target_vertical_out:
        raise AssertionError("d2 images are not target vertical cycles")
    e3_denominator = e2_denominator.stack(d2_images)
    d2_rank = int(e3_denominator.rank()) - int(e2_denominator.rank())

    d3_images = corrected_images((3, 2, 1))
    if d3_images * target_vertical_out:
        raise AssertionError("d3 images are not target vertical cycles")
    d3_rank = int(e3_denominator.stack(d3_images).rank()) \
        - int(e3_denominator.rank())
    return d2_rank, d3_rank


def filtered_h2_dimensions(boundaries, degree: int):
    """Compute the cellular filtration on total H2 in the chosen field."""

    if boundaries[3] * boundaries[2]:
        raise AssertionError("total degree-three boundaries are not cycles")

    full_boundary_rank = int(boundaries[3].rank())
    cumulative = []
    for maximum_q in range(3):
        supported_indices = [
            index
            for q in range(maximum_q + 1)
            for index in coordinate_indices(2, q, degree)
        ]
        restricted = boundaries[2].matrix_from_rows(supported_indices)
        supported_cycles = restricted.left_kernel().basis_matrix()
        embedded = matrix(
            boundaries[2].base_ring(),
            supported_cycles.nrows(),
            boundaries[2].nrows(),
            {
                (row, supported_indices[column]): value
                for (row, column), value in supported_cycles.dict().items()
            },
            sparse=True,
        )
        cumulative.append(
            int(boundaries[3].stack(embedded).rank()) - full_boundary_rank
        )

    graded = [
        cumulative[0],
        cumulative[1] - cumulative[0],
        cumulative[2] - cumulative[1],
    ]
    if any(dimension < 0 for dimension in graded):
        raise AssertionError("filtered H2 dimensions are not monotone")
    return {
        "filtration_dimensions": cumulative,
        "graded_dimensions": {
            "0,2": graded[0],
            "1,1": graded[1],
            "2,0": graded[2],
        },
    }


def permutation_from_vertical_generator(boundary, generator: int, degree: int):
    """Recover one vertex-stabilizer permutation from its mod-two boundary."""

    result = []
    for coefficient in range(degree):
        support = boundary.row(generator * degree + coefficient).support()
        if not support:
            result.append(coefficient)
            continue
        if len(support) != 2 or coefficient not in support:
            raise AssertionError("vertex boundary is not permutation minus identity")
        result.append(next(index for index in support if index != coefficient))
    return tuple(result)


def vertex_orbit_profile(boundaries, degree: int, coordinate: int):
    """Identify the finite S4 orbit supporting a q=0 representative."""

    if boundaries[1].base_ring().characteristic() != 2:
        return None
    permutations = [
        permutation_from_vertical_generator(boundaries[1], generator, degree)
        for generator in range(3)
    ]
    identity = tuple(range(degree))

    def compose(left, right):
        return tuple(left[right[index]] for index in range(degree))

    group = {identity}
    pending = [identity]
    while pending:
        left = pending.pop()
        for right in permutations:
            product = compose(left, right)
            if product not in group:
                group.add(product)
                pending.append(product)

    stabilizer = [element for element in group if element[coordinate] == coordinate]

    def element_order(element):
        power = identity
        for order in range(1, len(group) + 1):
            power = compose(element, power)
            if power == identity:
                return order
        raise AssertionError("permutation order exceeds group order")

    order_histogram = {}
    for element in stabilizer:
        order = element_order(element)
        order_histogram[str(order)] = order_histogram.get(str(order), 0) + 1
    return {
        "orbit": sorted({element[coordinate] for element in group}),
        "acting_group_order": len(group),
        "stabilizer_order": len(stabilizer),
        "stabilizer_element_order_histogram": order_histogram,
        "generator_restrictions": [
            [permutation[index] for index in sorted({
                element[coordinate] for element in group
            })]
            for permutation in permutations
        ],
    }


def q0_homology_representatives(boundaries, degree: int, graded_dimension: int):
    """Lift a basis of the q=0 graded H2 term and report its support."""

    supported_indices = coordinate_indices(2, 0, degree)
    restricted = boundaries[2].matrix_from_rows(supported_indices)
    local_cycles = restricted.left_kernel().basis_matrix()
    embedded = matrix(
        boundaries[2].base_ring(),
        local_cycles.nrows(),
        boundaries[2].nrows(),
        {
            (row, supported_indices[column]): value
            for (row, column), value in local_cycles.dict().items()
        },
        sparse=True,
    )
    cycle_space = embedded.row_space()
    boundary_space = boundaries[3].row_space()

    # In characteristic two the surviving projective classes have canonical
    # singleton representatives.  Certifying them directly is much cheaper
    # than constructing a quotient basis in the larger charts.
    if boundaries[2].base_ring().characteristic() == 2 and graded_dimension == 2:
        candidates = matrix(
            boundaries[2].base_ring(), 2, boundaries[2].nrows(),
            {(0, 0): 1, (1, 1): 1}, sparse=True,
        ).row_space()
        if not candidates.is_subspace(cycle_space):
            raise AssertionError("canonical singleton representatives are not cycles")
        if (boundary_space + candidates).dimension() - boundary_space.dimension() != 2:
            raise AssertionError("canonical singleton representatives are not independent")
        return [
            {
                "support_size": 1,
                "total_coordinates": [coordinate],
                "resolution_generators": [0],
                "coefficient_coordinates": [coordinate],
                "vertex_orbit": vertex_orbit_profile(
                    boundaries, degree, coordinate),
            }
            for coordinate in (0, 1)
        ]

    boundary_cycles = cycle_space.intersection(boundary_space)
    quotient = cycle_space.quotient(boundary_cycles)
    result = []
    for quotient_vector in quotient.basis():
        vector = quotient_vector.lift()
        support = [int(index) for index in vector.support()]
        result.append({
            "support_size": len(support),
            "total_coordinates": support,
            "resolution_generators": sorted({index // degree for index in support}),
            "coefficient_coordinates": sorted({index % degree for index in support}),
        })
    return result


def q0_singleton_class_profile(boundaries, degree: int):
    """Classify singleton cycles in the first q=0 resolution generator."""

    field = boundaries[2].base_ring()
    if field.cardinality() != 2:
        raise ValueError("the singleton class profile is a mod-two invariant")

    singleton_indices = [
        index for index in range(degree) if not boundaries[2].row(index)
    ]
    if len(singleton_indices) < 2:
        raise AssertionError("fewer than two singleton q=0 cycles")

    def unit(index):
        return matrix(
            field, 1, boundaries[2].nrows(), {(0, index): 1}, sparse=True
        ).row(0)

    boundary_space = boundaries[3].row_space()
    first = unit(singleton_indices[0])
    second = unit(singleton_indices[1])
    if boundaries[3].stack(matrix(field, [first, second])).rank() \
            - boundaries[3].rank() != 2:
        raise AssertionError("the first two singleton classes are dependent")

    classes = []
    for index in singleton_indices:
        candidate = unit(index)
        label = None
        for first_coefficient, second_coefficient in (
                (0, 0), (1, 0), (0, 1), (1, 1)):
            if candidate + first_coefficient * first \
                    + second_coefficient * second in boundary_space:
                label = [first_coefficient, second_coefficient]
                break
        if label is None:
            raise AssertionError("a singleton cycle lies outside the two classes")
        classes.append({"coordinate": int(index), "class": label})

    return {
        "count": len(singleton_indices),
        "classes": classes,
    }


def analyze(prime: int, modulus: int, prefix: Path):
    degree = prime**2 + prime + 1
    field = GF(modulus)
    boundaries = {
        total_degree: read_boundary(
            Path(f"{prefix}-d{total_degree}.tsv"), field)
        for total_degree in range(1, 4)
    }
    vertical = {}
    for total_degree in range(1, 4):
        for cellular_degree in range(total_degree):
            rank, source, target = vertical_rank(
                boundaries, total_degree, cellular_degree, degree)
            vertical[(cellular_degree, total_degree - cellular_degree)] = {
                "rank": rank,
                "source_dimension": source,
                "target_dimension": target,
            }

    e1_total_two = {}
    for cellular_degree in range(3):
        stabilizer_degree = 2 - cellular_degree
        chain_dimension = len([
            q for q in Q_BY_TOTAL_GENERATOR[2] if q == cellular_degree
        ]) * degree
        outgoing = vertical[(cellular_degree, stabilizer_degree)]["rank"] \
            if stabilizer_degree > 0 else 0
        incoming = vertical[(cellular_degree, stabilizer_degree + 1)]["rank"]
        e1_total_two[f"{cellular_degree},{stabilizer_degree}"] = (
            chain_dimension - outgoing - incoming
        )

    outgoing_h1 = horizontal_h1_rank(boundaries, degree)
    incoming_h1_rank = horizontal_image_rank(
        boundaries, total_degree=3, source_q=2, target_q=1, degree=degree)
    e2_1_1 = e1_total_two["1,1"] - outgoing_h1["rank"] - incoming_h1_rank
    if e2_1_1 < 0:
        raise AssertionError("horizontal E1 ranks violate the chain inequality")
    incoming_h2_rank = horizontal_image_rank(
        boundaries, total_degree=3, source_q=1, target_q=0, degree=degree)
    e2_0_2 = e1_total_two["0,2"] - incoming_h2_rank
    if e2_0_2 < 0:
        raise AssertionError("horizontal H2 image exceeds its target")
    d2_rank, d3_rank = higher_image_ranks(boundaries, degree)
    e3_0_2 = e2_0_2 - d2_rank
    if e3_0_2 < 0:
        raise AssertionError("filtered d2 image exceeds its E2 target")
    e4_0_2 = e3_0_2 - d3_rank
    if e4_0_2 < 0:
        raise AssertionError("filtered d3 image exceeds its E3 target")

    full_boundary_ranks = {
        str(total_degree): int(boundaries[total_degree].rank())
        for total_degree in (2, 3)
    }
    total_h2 = (
        boundaries[2].nrows()
        - full_boundary_ranks["2"]
        - full_boundary_ranks["3"]
    )
    filtered_h2 = filtered_h2_dimensions(boundaries, degree)
    if filtered_h2["filtration_dimensions"][-1] != total_h2:
        raise AssertionError("cellular filtration does not exhaust total H2")
    q0_representatives = q0_homology_representatives(
        boundaries, degree, filtered_h2["graded_dimensions"]["0,2"])
    if len(q0_representatives) != filtered_h2["graded_dimensions"]["0,2"]:
        raise AssertionError("q=0 representatives do not span the graded term")
    q0_singletons = q0_singleton_class_profile(boundaries, degree) \
        if modulus == 2 else None

    return {
        "prime": prime,
        "coefficient_characteristic": modulus,
        "projective_degree": degree,
        "vertical_blocks": {
            f"{q},{s}": value for (q, s), value in sorted(vertical.items())
        },
        "E1_total_degree_two_dimensions": e1_total_two,
        "E1_horizontal_H1_D8_to_H1_S4": outgoing_h1,
        "E1_horizontal_H1_cells_to_D8_image_rank": incoming_h1_rank,
        "E1_horizontal_H2_D8_to_S4_image_rank": incoming_h2_rank,
        "E2_1_1_dimension": e2_1_1,
        "E2_0_2_dimension": e2_0_2,
        "E2_d2_2_1_to_0_2_image_rank": d2_rank,
        "E3_0_2_dimension": e3_0_2,
        "E3_d3_3_0_to_0_2_image_rank": d3_rank,
        "E4_0_2_dimension": e4_0_2,
        "full_boundary_ranks": full_boundary_ranks,
        "full_H2_dimension": total_h2,
        "E_infinity_total_degree_two": filtered_h2,
        "E_infinity_q0_representatives": q0_representatives,
        "E_infinity_q0_singleton_class_profile": q0_singletons,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("prime", type=int)
    parser.add_argument("modulus", type=int, choices=(2, 3))
    parser.add_argument("prefix", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    result = analyze(args.prime, args.modulus, args.prefix)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
