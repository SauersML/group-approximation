"""Verify one prime-independent four-term relation in the q=0 residue.

The total degree-three chain is specified by resolution-generator and
coefficient-coordinate pairs.  Its mod-two boundary must be the difference
of ordinary singleton cycles 1 and 8 in the first q=0 generator.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from sage.all import GF, matrix

from sl3_projective_derived_e1 import read_boundary


RELATION_SUPPORT = (
    (10, 8),
    (11, 1),
    (11, 8),
    (12, 8),
)


def verify(prime: int, prefix: Path):
    degree = prime**2 + prime + 1
    boundary2 = read_boundary(Path(f"{prefix}-d2.tsv"), GF(2))
    boundary3 = read_boundary(Path(f"{prefix}-d3.tsv"), GF(2))
    chain = matrix(
        GF(2),
        1,
        boundary3.nrows(),
        {(0, generator * degree + coordinate): 1
         for generator, coordinate in RELATION_SUPPORT},
        sparse=True,
    )
    image = chain * boundary3
    expected = matrix(
        GF(2), 1, boundary3.ncols(), {(0, 1): 1, (0, 8): 1}, sparse=True
    )
    if image != expected:
        raise AssertionError("the fixed chain does not have the expected boundary")
    if boundary2.row(1) or boundary2.row(8):
        raise AssertionError("an endpoint is not a total degree-two cycle")
    return {
        "prime": prime,
        "projective_degree": degree,
        "chain_support_size": len(RELATION_SUPPORT),
        "endpoint_coordinates": [1, 8],
        "verified": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("prime", type=int)
    parser.add_argument("prefix", type=Path)
    args = parser.parse_args()
    print(json.dumps(verify(args.prime, args.prefix), sort_keys=True))


if __name__ == "__main__":
    main()
