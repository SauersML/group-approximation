"""Classify atlas survivors up to conjugacy and inversion in A8 * A8.

The input is the exact JSON artifact produced by
atlas_perfect_overlap_scan.py. Matrix multiplication and inversion are
performed over F_2. The classifier uses the standard conjugacy normal form
for a free product: cyclically reduced words of length at least two are
conjugate exactly when their syllable lists differ by a cyclic rotation.
"""

import argparse
import json

import numpy as np

from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key


IDENTITY_KEY = matrix_key(I4)


def decode_word(record):
    return [
        (
            letter["factor"],
            np.frombuffer(
                bytes.fromhex(letter["matrix_f2_hex"]), dtype=np.uint8
            ).reshape(4, 4),
        )
        for letter in record["word"]
    ]


def free_reduce(word):
    stack = []
    for factor, matrix in word:
        if matrix_key(matrix) == IDENTITY_KEY:
            continue
        if stack and stack[-1][0] == factor:
            product = gf2_mul(stack[-1][1], matrix)
            stack.pop()
            if matrix_key(product) != IDENTITY_KEY:
                stack.append((factor, product))
        else:
            stack.append((factor, matrix))
    return stack


def cyclic_reduce(word):
    """Return a cyclically reduced conjugate of a free-product word."""
    word = free_reduce(word)
    while len(word) > 1 and word[0][0] == word[-1][0]:
        factor = word[0][0]
        # If word = x u y, conjugating by x^{-1} gives u y x.
        product = gf2_mul(word[-1][1], word[0][1])
        word = word[1:-1]
        if matrix_key(product) != IDENTITY_KEY:
            word.append((factor, product))
        word = free_reduce(word)
    return word


def invert_word(word):
    return [(factor, gf2_inv(matrix)) for factor, matrix in reversed(word)]


def word_key(word):
    return tuple((factor, matrix_key(matrix).hex()) for factor, matrix in word)


def rotation_keys(word):
    return [
        word_key(word[offset:] + word[:offset])
        for offset in range(len(word))
    ]


def oriented_key(word):
    word = cyclic_reduce(word)
    return min(rotation_keys(word))


def unoriented_key(word):
    word = cyclic_reduce(word)
    return min(rotation_keys(word) + rotation_keys(invert_word(word)))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    args = parser.parse_args()

    with open(args.input, "r", encoding="utf-8") as stream:
        data = json.load(stream)

    classes = {}
    for record in data["survivor_records"]:
        word = decode_word(record)
        classes.setdefault(unoriented_key(word), []).append(record)

    rows = []
    for records in classes.values():
        records.sort(key=lambda record: record["word_index"])
        representative = records[0]
        word = decode_word(representative)
        rows.append({
            "representative_word_index": representative["word_index"],
            "cyclically_reduced_length": len(cyclic_reduce(word)),
            "self_inverse_up_to_conjugacy": (
                oriented_key(word) == oriented_key(invert_word(word))
            ),
            "members": [
                {
                    "word_index": record["word_index"],
                    "length": record["length"],
                }
                for record in records
            ],
        })
    rows.sort(key=lambda row: row["representative_word_index"])

    result = {
        "survivors": len(data["survivor_records"]),
        "conjugacy_or_inverse_classes": len(rows),
        "class_sizes": [len(row["members"]) for row in rows],
        "classes": rows,
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
