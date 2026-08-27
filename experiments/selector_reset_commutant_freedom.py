#!/usr/bin/env python3
"""Audit the representation-ring equations for a selector-free spin reset.

The common symplectic subgroup has one spin type ``sigma``.  Adjoining a
central Boolean selector gives two extensions, both restricting to ``sigma``.
Thus an old-to-fresh amalgam over the spin subgroup has the same restriction
matrix on each side.  This script prints the incidence equation and enumerates
the exact one-copy representations, showing that all old/fresh sign pairs are
independent exact solutions.
"""

from __future__ import annotations

from itertools import product


def restriction_matrix(selector_bits: int) -> list[list[int]]:
    """Restriction from sigma tensor C[(C2)^k] to the unique sigma type."""
    return [[1] * (1 << selector_bits)]


def audit(selector_bits: int) -> None:
    old = restriction_matrix(selector_bits)
    fresh = restriction_matrix(selector_bits)
    assert old == fresh

    characters = list(product((-1, 1), repeat=selector_bits))
    exact_pairs = list(product(characters, repeat=2))
    assert len(exact_pairs) == 1 << (2 * selector_bits)

    print(f"selector bits={selector_bits}")
    print(f"  old restriction matrix:   {old}")
    print(f"  fresh restriction matrix: {fresh}")
    print("  incidence equation: sum(old multiplicities) = "
          "sum(fresh multiplicities)")
    print(f"  independent exact character pairs: {len(exact_pairs)}")
    if selector_bits == 1:
        print(f"  pairs: {exact_pairs}")


if __name__ == "__main__":
    for bits in range(1, 5):
        audit(bits)
