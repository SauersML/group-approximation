#!/usr/bin/env python3
"""Audit literal tensor covariance in the order-128 support packet.

The covariant Wedderburn detector compares commutant *algebras*.  A much
stronger detector would use two coefficient representations V_+, V_- with

    S tensor V_+ == S tensor V_-

for every allowed packet simple S, but not for the forbidden simple.  This
script verifies exactly that no such virtual-character difference exists.
It also performs a bounded search for an alpha-covariant coefficient that is
isotypic for the packet centre, the form needed by a Stone--von Neumann
coefficient exactifier.

Only the Python standard library is used.  All character and fusion values
are integral.
"""
from __future__ import annotations

import argparse
from itertools import combinations_with_replacement, product

import schur_packet_tensor_fusion_search as packet


def rank_mod(rows: list[list[int]], prime: int) -> int:
    work = [[entry % prime for entry in row] for row in rows]
    if not work:
        return 0
    pivot_row = 0
    for column in range(len(work[0])):
        pivot = next(
            (row for row in range(pivot_row, len(work)) if work[row][column]),
            None,
        )
        if pivot is None:
            continue
        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        inverse = pow(work[pivot_row][column], -1, prime)
        work[pivot_row] = [(inverse * entry) % prime for entry in work[pivot_row]]
        for row in range(len(work)):
            if row == pivot_row or not work[row][column]:
                continue
            coefficient = work[row][column]
            work[row] = [
                (left - coefficient * right) % prime
                for left, right in zip(work[row], work[pivot_row])
            ]
        pivot_row += 1
    return pivot_row


def alpha_element(element: tuple[int, ...]) -> tuple[int, ...]:
    """The involution from (CWD2), in p,p,q,q,J,z_e,z_f coordinates."""
    p_1, p_2, q_1, q_2, j, z_e, z_f = element
    return p_1, p_2, q_1, q_1 ^ q_2, z_e, j, z_f


def row_vector_matrix(bits: tuple[int, ...], matrix: tuple[tuple[int, ...], ...]) -> tuple[int, ...]:
    return tuple(
        sum(bits[row] & matrix[row][column] for row in range(len(bits))) & 1
        for column in range(len(matrix[0]))
    )


def automorphism_element(
    element: tuple[int, ...],
    automorphism: tuple[packet.Matrix2F, packet.Matrix2F, packet.Matrix3F],
) -> tuple[int, ...]:
    p_change, q_change, center_change = automorphism
    return (
        row_vector_matrix(element[:2], p_change)
        + row_vector_matrix(element[2:4], q_change)
        + row_vector_matrix(element[4:], packet.transpose3(center_change))
    )


def audit(max_isotypic_summands: int) -> None:
    irreps = packet.irreps()
    irrep_count = len(irreps)
    allowed_indices = [
        index
        for index, irrep in enumerate(irreps)
        if irrep.character in packet.ALLOWED_J_MINUS
    ]
    forbidden_indices = [
        index
        for index, irrep in enumerate(irreps)
        if irrep.character == packet.FORBIDDEN
    ]

    support_counts: dict[tuple[bool, bool], int] = {}
    for element_index, _ in enumerate(packet.GROUP_ELEMENTS):
        allowed_nonzero = any(
            irreps[index].values[element_index] != 0 for index in allowed_indices
        )
        forbidden_nonzero = any(
            irreps[index].values[element_index] != 0 for index in forbidden_indices
        )
        support_counts[(allowed_nonzero, forbidden_nonzero)] = (
            support_counts.get((allowed_nonzero, forbidden_nonzero), 0) + 1
        )
        if forbidden_nonzero and not allowed_nonzero:
            raise AssertionError("forbidden character support escaped allowed support")

    fusion = [
        [packet.fusion(source, coefficient.values, irreps) for coefficient in irreps]
        for source in irreps
    ]
    allowed_rows = [
        [fusion[source][coefficient][target] for coefficient in range(irrep_count)]
        for source in allowed_indices
        for target in range(irrep_count)
    ]
    forbidden_rows = [
        [fusion[source][coefficient][target] for coefficient in range(irrep_count)]
        for source in forbidden_indices
        for target in range(irrep_count)
    ]
    for prime in (2, 3, 5, 101):
        allowed_rank = rank_mod(allowed_rows, prime)
        joined_rank = rank_mod(allowed_rows + forbidden_rows, prime)
        if allowed_rank != 26 or joined_rank != allowed_rank:
            raise AssertionError((prime, allowed_rank, joined_rank))

    # A diagonal HNN edge can twist the source and coefficient factors by
    # different packet automorphisms.  Check the stronger two-coefficient
    # system for all 4 x 4 such pairs.  If x,y are the two virtual coefficient
    # vectors, its rows express S*x=(S pulled by gamma)*(y pulled by delta).
    automorphism_irreps: list[list[int]] = []
    position = {element: index for index, element in enumerate(packet.GROUP_ELEMENTS)}
    for automorphism in packet.packet_linear_automorphisms():
        permutation = []
        for irrep in irreps:
            pulled_values = tuple(
                irrep.values[position[automorphism_element(element, automorphism)]]
                for element in packet.GROUP_ELEMENTS
            )
            matches = [
                index
                for index, target in enumerate(irreps)
                if packet.inner(pulled_values, target.values) == 1
            ]
            if len(matches) != 1:
                raise AssertionError((irrep.label, matches))
            permutation.append(matches[0])
        automorphism_irreps.append(permutation)

    twisted_rank_profiles: dict[tuple[int, int], tuple[int, int]] = {}
    for source_automorphism, source_permutation in enumerate(automorphism_irreps):
        for coefficient_automorphism, coefficient_permutation in enumerate(
            automorphism_irreps
        ):
            def covariance_rows(source_indices: list[int]) -> list[list[int]]:
                return [
                    [fusion[source][coefficient][target] for coefficient in range(irrep_count)]
                    + [
                        -fusion[source_permutation[source]][
                            coefficient_permutation[coefficient]
                        ][target]
                        for coefficient in range(irrep_count)
                    ]
                    for source in source_indices
                    for target in range(irrep_count)
                ]

            twisted_allowed = covariance_rows(allowed_indices)
            twisted_forbidden = covariance_rows(forbidden_indices)
            allowed_rank = rank_mod(twisted_allowed, 101)
            joined_rank = rank_mod(twisted_allowed + twisted_forbidden, 101)
            if joined_rank != allowed_rank:
                raise AssertionError(
                    (source_automorphism, coefficient_automorphism, allowed_rank, joined_rank)
                )
            twisted_rank_profiles[(source_automorphism, coefficient_automorphism)] = (
                allowed_rank,
                joined_rank,
            )

    alpha_irrep = []
    for irrep in irreps:
        pulled_values = tuple(
            irrep.values[position[alpha_element(element)]]
            for element in packet.GROUP_ELEMENTS
        )
        matches = [
            index
            for index, target in enumerate(irreps)
            if packet.inner(pulled_values, target.values) == 1
        ]
        if len(matches) != 1:
            raise AssertionError((irrep.label, matches))
        alpha_irrep.append(matches[0])

    source_representatives = {
        character: next(irrep for irrep in irreps if irrep.character == character)
        for character in (*packet.ALLOWED_J_MINUS, packet.FORBIDDEN)
    }
    fusion_grams: dict[packet.Bit3, list[list[int]]] = {}
    for character, source in source_representatives.items():
        twisted = [
            packet.tensor_values(source.values, coefficient.values)
            for coefficient in irreps
        ]
        fusion_grams[character] = [
            [packet.inner(left, right) for right in twisted] for left in twisted
        ]

    def commutant_dimension(indices: tuple[int, ...], character: packet.Bit3) -> int:
        gram = fusion_grams[character]
        return sum(gram[left][right] for left in indices for right in indices)

    tested = 0
    candidates = 0
    for central_character in product((0, 1), repeat=3):
        pool = [
            index
            for index, irrep in enumerate(irreps)
            if irrep.character == central_character
        ]
        for summand_count in range(1, max_isotypic_summands + 1):
            for indices in combinations_with_replacement(pool, summand_count):
                tested += 1
                alpha_indices = tuple(sorted(alpha_irrep[index] for index in indices))
                allowed_flat = all(
                    commutant_dimension(indices, character)
                    == commutant_dimension(alpha_indices, character)
                    for character in packet.ALLOWED_J_MINUS
                )
                forbidden_distinct = (
                    commutant_dimension(indices, packet.FORBIDDEN)
                    != commutant_dimension(alpha_indices, packet.FORBIDDEN)
                )
                candidates += int(allowed_flat and forbidden_distinct)
    if candidates:
        raise AssertionError("found a centre-isotypic alpha-covariant detector")

    print("character support counts (allowed_nonzero, forbidden_nonzero):")
    for key in sorted(support_counts):
        print(f"  {key}: {support_counts[key]}")
    print("literal tensor-annihilator rank: 26; nullity: 12 (four primes agree)")
    print("adding every forbidden multiplication equation leaves rank 26")
    rank_histogram: dict[int, int] = {}
    for allowed_rank, joined_rank in twisted_rank_profiles.values():
        if allowed_rank != joined_rank:
            raise AssertionError((allowed_rank, joined_rank))
        rank_histogram[allowed_rank] = rank_histogram.get(allowed_rank, 0) + 1
    print(
        "all 16 independently twisted covariance systems remain forbidden-blind; "
        f"allowed-rank histogram {dict(sorted(rank_histogram.items()))}"
    )
    print(
        "centre-isotypic alpha screen: "
        f"{tested} coefficients through {max_isotypic_summands} summands; "
        "0 candidates"
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-isotypic-summands", type=int, default=6)
    arguments = parser.parse_args()
    audit(arguments.max_isotypic_summands)
