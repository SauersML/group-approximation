"""Trace the exact Leavitt-prefix evaluation of collision word 19243.

This avoids the radius-five enumeration: the decoded word is written using
the three named transvections and every intermediate prefix expansion is
printed exactly.  It is a diagnostic for comparing the prefix algebra with
a proposed two-by-two corner model.
"""

import json

from atlas_kernel_collision_enumerator import ONE
from atlas_two_chart_search import (
    gf2_mul,
    leavitt_chart_element,
    leavitt_is_one,
    leavitt_mul,
    matrix_key,
    transvection,
)


def encode(value):
    return sorted({
        "".join(map(str, left)) + ":" + "".join(map(str, right))
        for left, right in value
    })


def main():
    x = transvection(0, 1)
    y = transvection(1, 0)
    q = transvection(2, 3)
    word = (
        (2, gf2_mul(y, x)),
        (1, q),
        (2, y),
        (1, q),
        (2, gf2_mul(x, y)),
        (1, q),
        (2, x),
        (1, q),
    )
    value = ONE
    stages = []
    for factor, matrix in word:
        value = leavitt_mul(value, leavitt_chart_element(factor, matrix))
        stages.append(encode(value))
    print(json.dumps({
        "word": [
            {"factor": factor, "matrix_f2_hex": matrix_key(matrix).hex()}
            for factor, matrix in word
        ],
        "stages": stages,
        "final_is_one": leavitt_is_one(value),
    }, indent=2))


if __name__ == "__main__":
    main()
