#!/usr/bin/env python3
"""Exact audit linking the minimal A8 four-cycle to the raw S3 detector.

The raw Reynolds audit identifies its two second-chart involutions by exact
matrix hex.  This script freezes their coordinates in the standard GL(4,2)
chart and an eight-letter word for the missing reverse transvection t21 in the
minimal cycle generators t01,t12,t23,t30.
"""
import json
import numpy as np

from atlas_two_chart_search import I4, gf2_mul, matrix_key


def transvection(row, col):
    out = I4.copy()
    out[row, col] ^= 1
    return out


def matrix(hex_value):
    return np.frombuffer(bytes.fromhex(hex_value), dtype=np.uint8).reshape(4, 4).copy()


T = {
    "t01": transvection(0, 1),
    "t12": transvection(1, 2),
    "t23": transvection(2, 3),
    "t30": transvection(3, 0),
}
RAW_A_HEX = "01000000000100000001010000000001"
RAW_B_HEX = "01000000000101000000010000000001"
T21_WORD = ("t01", "t30", "t23", "t30", "t01", "t30", "t23", "t30")


def eval_word(word):
    value = I4.copy()
    for name in word:
        value = gf2_mul(value, T[name])
    return value


def main():
    raw_a = matrix(RAW_A_HEX)
    raw_b = matrix(RAW_B_HEX)
    t21 = transvection(2, 1)
    assert matrix_key(raw_a) == matrix_key(t21)
    assert matrix_key(raw_b) == matrix_key(T["t12"])
    assert matrix_key(eval_word(T21_WORD)) == matrix_key(t21)

    counts = {name: T21_WORD.count(name) for name in T}
    cauchy_constant = sum(count * count for count in counts.values())
    assert counts == {"t01": 2, "t12": 0, "t23": 2, "t30": 4}
    assert cauchy_constant == 24

    print(json.dumps({
        "raw_S3_first_involution": "t21",
        "raw_S3_second_involution": "t12",
        "t21_word_in_four_cycle": list(T21_WORD),
        "generator_counts": counts,
        "cauchy_constant": cauchy_constant,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
