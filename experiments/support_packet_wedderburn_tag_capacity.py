#!/usr/bin/env python3
"""Enumerate non-character tag capacity in the order-128 support packet.

Two coefficient representations are placed in the same allowed class when
they have the same dimension and their tensor-product commutants have the
same Wedderburn type on every irreducible source above the three allowed
J=-1 central characters.  Inside one such class, distinct Wedderburn types
above the unique forbidden 101 source are genuinely different
non-character tags.

The computation is exact.  A Wedderburn signature is encoded by histograms
of nonzero target multiplicities, separated by target irrep dimension.  This
is equivalent to sorting the pairs (multiplicity, target dimension), but is
considerably faster to compare exhaustively.
"""
from __future__ import annotations

import argparse
import json
import zlib
from collections import defaultdict
from itertools import combinations_with_replacement
from pathlib import Path
from time import monotonic

from schur_packet_tensor_fusion_search import (
    ALLOWED_J_MINUS,
    FORBIDDEN,
    fusion,
    irreps,
)


def signature(multiplicities: tuple[int, ...], dimensions: tuple[int, ...]) -> bytes:
    """Encode the exact commutant Wedderburn type as a compact byte string."""
    pairs = sorted(
        (multiplicity, dimension)
        for multiplicity, dimension in zip(multiplicities, dimensions)
        if multiplicity
    )
    if any(multiplicity > 255 or dimension > 255 for multiplicity, dimension in pairs):
        raise AssertionError("signature no longer fits in the exact byte encoding")
    output = bytearray((len(pairs),))
    for multiplicity, dimension in pairs:
        output.extend((multiplicity, dimension))
    return bytes(output)


def label(indices: tuple[int, ...], all_irreps) -> str:
    return "+".join(all_irreps[index].label for index in indices)


def enumerate_capacity(summand_count: int) -> dict[str, object]:
    all_irreps = irreps()
    dimensions = tuple(irrep.dimension for irrep in all_irreps)
    allowed_sources = tuple(
        index
        for index, irrep in enumerate(all_irreps)
        if irrep.character in ALLOWED_J_MINUS
    )
    forbidden_sources = tuple(
        index
        for index, irrep in enumerate(all_irreps)
        if irrep.character == FORBIDDEN
    )
    assert len(allowed_sources) == 12
    assert len(forbidden_sources) == 1
    forbidden_source = forbidden_sources[0]

    fusion_tensor = tuple(
        tuple(tuple(fusion(source, coefficient.values, all_irreps)) for coefficient in all_irreps)
        for source in all_irreps
    )

    # Lossless compression is important at five summands: the number of exact
    # allowed keys grows sharply, while the signatures themselves contain
    # long repeated Pauli-block patterns.  Unlike a digest, the compressed
    # byte string is an injective key because it can be decompressed exactly.
    # compressed allowed key -> forbidden signature -> first exact witness
    classes: dict[bytes, dict[bytes, tuple[int, ...]]] = defaultdict(dict)
    coefficient_count = 0
    started = monotonic()

    for indices in combinations_with_replacement(range(len(all_irreps)), summand_count):
        coefficient_count += 1
        coefficient_dimension = sum(dimensions[index] for index in indices)
        if coefficient_dimension > 255:
            raise AssertionError("dimension no longer fits in exact byte encoding")

        allowed_key = bytearray((coefficient_dimension,))
        for source in allowed_sources:
            multiplicities = tuple(
                sum(fusion_tensor[source][coefficient][target] for coefficient in indices)
                for target in range(len(all_irreps))
            )
            allowed_key.extend(signature(multiplicities, dimensions))

        forbidden_multiplicities = tuple(
            sum(fusion_tensor[forbidden_source][coefficient][target] for coefficient in indices)
            for target in range(len(all_irreps))
        )
        forbidden_signature = signature(forbidden_multiplicities, dimensions)
        compressed_allowed_key = zlib.compress(bytes(allowed_key), level=1)
        classes[compressed_allowed_key].setdefault(forbidden_signature, indices)

    maximum_capacity = max(len(forbidden_types) for forbidden_types in classes.values())
    maximum_classes = [
        (allowed_key, forbidden_types)
        for allowed_key, forbidden_types in classes.items()
        if len(forbidden_types) == maximum_capacity
    ]

    witnesses = []
    for compressed_allowed_key, forbidden_types in maximum_classes[:16]:
        allowed_key = zlib.decompress(compressed_allowed_key)
        entries = []
        for forbidden_signature, indices in forbidden_types.items():
            entries.append(
                {
                    "coefficient": label(indices, all_irreps),
                    "indices": list(indices),
                    "forbidden_wedderburn_signature_hex": forbidden_signature.hex(),
                }
            )
        witnesses.append(
            {
                "coefficient_dimension": allowed_key[0],
                "allowed_key_hex": allowed_key.hex(),
                "forbidden_types": entries,
            }
        )

    capacity_histogram: dict[str, int] = defaultdict(int)
    for forbidden_types in classes.values():
        capacity_histogram[str(len(forbidden_types))] += 1

    return {
        "group_order": 128,
        "irrep_count": len(all_irreps),
        "allowed_source_count": len(allowed_sources),
        "forbidden_source_count": len(forbidden_sources),
        "summand_count": summand_count,
        "coefficient_count": coefficient_count,
        "allowed_equivalence_class_count": len(classes),
        "maximum_forbidden_tag_capacity": maximum_capacity,
        "number_of_maximum_classes": len(maximum_classes),
        "capacity_histogram": dict(sorted(capacity_histogram.items(), key=lambda item: int(item[0]))),
        "maximum_class_witnesses": witnesses,
        "elapsed_seconds": monotonic() - started,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("summand_count", type=int, choices=(1, 2, 3, 4, 5))
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()
    result = enumerate_capacity(arguments.summand_count)
    encoded = json.dumps(result, indent=2, sort_keys=True)
    if arguments.output:
        arguments.output.write_text(encoded + "\n")
    print(encoded)


if __name__ == "__main__":
    main()
