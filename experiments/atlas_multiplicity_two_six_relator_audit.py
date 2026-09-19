#!/usr/bin/env python3
"""Exact GF(2) audit of the multiplicity-two frame on the six Atlas rows."""

import json
from pathlib import Path


RELATORS = ("s_0", "s_11", "s_30", "s_44", "s_55", "c_19243")
FRAME = int("401004080301c030", 16)
IDENTITY = [1 << index for index in range(8)]


def multiply(left, right):
    output = []
    for row in left:
        value = 0
        while row:
            bit = row & -row
            value ^= right[bit.bit_length() - 1]
            row ^= bit
        output.append(value)
    return output


def inverse(value):
    rows = [value[index] | (1 << (8 + index)) for index in range(8)]
    for column in range(8):
        pivot = next(index for index in range(column, 8)
                     if (rows[index] >> column) & 1)
        rows[column], rows[pivot] = rows[pivot], rows[column]
        for index in range(8):
            if index != column and ((rows[index] >> column) & 1):
                rows[index] ^= rows[column]
    return [(rows[index] >> 8) & 0xff for index in range(8)]


def unpack(value):
    return [(value >> (8 * index)) & 0xff for index in range(8)]


def pack(value):
    return sum(row << (8 * index) for index, row in enumerate(value))


def lift_binary_matrix(encoded):
    """Tensor the stored 4 by 4 binary matrix with the 2 by 2 identity."""
    entries = bytes.fromhex(encoded)
    rows = [0] * 8
    for row in range(4):
        for column in range(4):
            if entries[4 * row + column]:
                rows[2 * row] |= 1 << (2 * column)
                rows[2 * row + 1] |= 1 << (2 * column + 1)
    return rows


def rank(value):
    rows = value[:]
    pivot = 0
    for column in range(8):
        found = next((index for index in range(pivot, len(rows))
                      if (rows[index] >> column) & 1), None)
        if found is None:
            continue
        rows[pivot], rows[found] = rows[found], rows[pivot]
        for index in range(len(rows)):
            if index != pivot and ((rows[index] >> column) & 1):
                rows[index] ^= rows[pivot]
        pivot += 1
    return pivot


def order(value):
    power = IDENTITY
    for exponent in range(1, 65):
        power = multiply(power, value)
        if power == IDENTITY:
            return exponent
    raise AssertionError("unexpected order above 64")


def main():
    here = Path(__file__).resolve().parent
    record = json.loads(
        (here / "atlas-six-relator-relative-pieces.json").read_text()
    )
    frame = unpack(FRAME)
    frame_inverse = inverse(frame)
    rows = {}
    for name in RELATORS:
        value = IDENTITY
        for factor, encoded in record["relators"][name]["word"]:
            letter = lift_binary_matrix(encoded)
            if factor == 2:
                letter = multiply(multiply(frame_inverse, letter), frame)
            value = multiply(value, letter)
        rows[name] = {
            "value": f"{pack(value):016x}",
            "is_identity": value == IDENTITY,
            "order": order(value),
            "rank_value_minus_identity": rank(
                [value[index] ^ IDENTITY[index] for index in range(8)]
            ),
        }

    assert rows["c_19243"]["is_identity"]
    assert all(not rows[name]["is_identity"] for name in RELATORS[:5])
    assert all(rows[name]["order"] == 2 for name in RELATORS[:5])
    assert all(rows[name]["rank_value_minus_identity"] == 2
               for name in RELATORS[:5])
    stacked = []
    cumulative_ranks = {}
    for name in RELATORS[:5]:
        value = unpack(int(rows[name]["value"], 16))
        stacked.extend(value[index] ^ IDENTITY[index] for index in range(8))
        cumulative_ranks[name] = rank(stacked)
    assert cumulative_ranks == {
        "s_0": 2, "s_11": 4, "s_30": 6, "s_44": 6, "s_55": 7,
    }
    print(json.dumps({
        "field": "GF(2)",
        "frame": f"{FRAME:016x}",
        "identity": f"{pack(IDENTITY):016x}",
        "cumulative_boundary_residual_ranks": cumulative_ranks,
        "common_boundary_fixed_space_dimension": 1,
        "rows": rows,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
