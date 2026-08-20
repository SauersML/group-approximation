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

    position = {element: index for index, element in enumerate(packet.GROUP_ELEMENTS)}
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
