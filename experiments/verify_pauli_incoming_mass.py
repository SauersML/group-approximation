#!/usr/bin/env python3
"""Derive the Pauli incoming-mass certificate from the exact block table."""

import json
from fractions import Fraction
from pathlib import Path


TABLE = Path(__file__).with_name(
    "atlas-transported-coefficient-raw-character-mixing.json"
)


def matrix_sum(rows):
    return sum((Fraction(entry) for row in rows for entry in row), Fraction())


data = json.loads(TABLE.read_text(encoding="utf-8"))
mass_0 = matrix_sum(data["transported_B0_block_masses"])
mass_1 = matrix_sum(data["transported_B1_block_masses"])
total = mass_0 + mass_1
corner = 4 * Fraction(data["raw_character_trace"])
ordered_overlap_floor = total * total / corner - total

assert mass_0 == Fraction(3, 8)
assert mass_1 == Fraction(1, 4)
assert total == Fraction(5, 8)
assert corner == Fraction(1, 2)
assert ordered_overlap_floor == Fraction(5, 32)

print(
    "verified:",
    f"m0={mass_0}",
    f"m1={mass_1}",
    f"total={total}",
    f"corner={corner}",
    f"overlap_floor={ordered_overlap_floor}",
)
