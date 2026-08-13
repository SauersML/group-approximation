"""Print selected exact collision-tree words and their chart projections.

This is a small diagnostic wrapper around the archived radius-five atlas
enumerator.  It does not search a new parameter space: it reconstructs only
the named spanning-tree words needed for the symbolic holonomy audit.
"""

import argparse
import json

from atlas_kernel_collision_enumerator import (
    encode_word,
    enumerate_ball,
    evaluate_word,
    factor_projections,
    spanning_tree_kernel_words,
)
from atlas_two_chart_search import I4, leavitt_is_one, matrix_key


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("indices", type=int, nargs="+")
    parser.add_argument("--radius", type=int, default=5)
    parser.add_argument(
        "--boundary",
        action="store_true",
        help="index the nontrivial factor-projection sublist",
    )
    args = parser.parse_args()

    states, _ = enumerate_ball(args.radius)
    words, _, _ = spanning_tree_kernel_words(states)
    if args.boundary:
        identity = matrix_key(I4)
        words = [word for word in words if any(
            matrix_key(projection) != identity
            for projection in factor_projections(word)
        )]
    records = []
    for index in args.indices:
        word = words[index]
        projections = factor_projections(word)
        records.append({
            "index": index,
            "length": len(word),
            "word": encode_word(word),
            "leavitt_is_one": leavitt_is_one(evaluate_word(word)),
            "factor_projection_hex": [
                matrix_key(value).hex() for value in projections
            ],
        })
    print(json.dumps(records, indent=2))


if __name__ == "__main__":
    main()
