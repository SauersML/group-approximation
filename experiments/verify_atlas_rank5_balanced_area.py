"""Verify the exact rank-five Atlas packet and balanced-area certificate.

The default verification is lightweight: it rebuilds the deterministic sparse
packet, binds the archived row to its source word, checks both canonical
SHA-256 digests, and replays the polynomial Bezout identity over ``Q``.
Passing ``--recompute-row`` additionally recomputes the archived balanced-area
row from the source word by the independent sparse collector (about one minute
on the original host).
"""

import argparse
from fractions import Fraction
import json

import atlas_relator_rank5_complete_packet as complete_packet
import atlas_three_mode_balanced_area as balanced_area


EXPECTED_PACKET_SHA256 = (
    "9e751115287b18fbe847309379d2710ffa0b1466c836d32ff4ec24446e6c2b99"
)
EXPECTED_TABLE_SHA256 = (
    "bd205a6f30584f8f2edaecded6f9b98228573f3277333661118a72b05c5aeafd"
)


def decode_fraction(encoded):
    if len(encoded) != 2:
        raise AssertionError("a rational must be encoded by [numerator, denominator]")
    return Fraction(encoded[0], encoded[1])


def decode_polynomial(encoded):
    return tuple(decode_fraction(coefficient) for coefficient in encoded)


def decode_laurent_row(row):
    polynomial = {}
    for area, numerator, denominator in row["coefficients"]:
        if area in polynomial:
            raise AssertionError("duplicate Laurent exponent")
        coefficient = Fraction(numerator, denominator)
        if not coefficient:
            raise AssertionError("zero coefficient must not be serialized")
        polynomial[area] = coefficient
    return polynomial


def verify(path, recompute_row):
    with open(path) as handle:
        artifact = json.load(handle)

    metadata = artifact["metadata"]
    rows = artifact["relators"]
    packet_metadata, packet_entries = complete_packet.assemble(False)

    assert packet_metadata["word_list_sha256"] == EXPECTED_PACKET_SHA256
    assert metadata["packet_word_list_sha256"] == EXPECTED_PACKET_SHA256
    assert metadata["packet_entries"] == len(packet_entries) == 4_648
    assert metadata["processed_entries"] == len(rows)
    assert balanced_area.output_digest(rows) == EXPECTED_TABLE_SHA256
    assert metadata["balanced_table_sha256"] == EXPECTED_TABLE_SHA256

    relation_polynomials = {}
    relation_shifts = {}
    for row in rows:
        index = row["index"]
        if not 0 <= index < len(packet_entries):
            raise AssertionError("row index lies outside the packet")
        source = packet_entries[index]
        assert (row["source"], row["name"], row["syllables"]) == (
            source["source"], source["name"], source["syllables"]
        )
        polynomial = decode_laurent_row(row)
        shift, relation = balanced_area.laurent_relation(polynomial)
        assert shift == row["relation_shift"]
        relation_shifts[index] = shift
        relation_polynomials[index] = relation

        if recompute_row:
            word = balanced_area.deserialize_word(source)
            recomputed, peak = balanced_area.collect_word(
                word, metadata["state_cap"]
            )
            assert recomputed == polynomial
            assert peak == row["peak_sparse_states"]

    decision = metadata["gcd_decision"]
    certified = ()
    used_indices = set()
    for term in decision["bezout_certificate"]:
        index = term["index"]
        if index in used_indices:
            raise AssertionError("duplicate Bezout row")
        used_indices.add(index)
        certified = balanced_area.poly_add(
            certified,
            balanced_area.poly_mul(
                decode_polynomial(term["multiplier"]),
                relation_polynomials[index],
            ),
        )

    running_gcd = decode_polynomial(decision["running_gcd"])
    assert certified == running_gcd == (Fraction(1),)
    assert decision["common_nonzero_root_excluded"] is True

    # Freeze the literal one-row mathematical certificate, rather than merely
    # accepting mutually consistent metadata from the artifact.
    assert len(rows) == 1
    assert rows[0]["index"] == 0
    assert rows[0]["name"] == "root_12_1e"
    assert decode_laurent_row(rows[0]) == {
        0: Fraction(16_953_689, 41_287_680)
    }
    assert relation_shifts[0] == 0
    assert relation_polynomials[0] == (
        Fraction(-24_333_991, 41_287_680),
    )

    print(
        json.dumps(
            {
                "bezout_identity": "verified over Q",
                "packet_entries": len(packet_entries),
                "packet_sha256": EXPECTED_PACKET_SHA256,
                "recomputed_row": recompute_row,
                "table_sha256": EXPECTED_TABLE_SHA256,
                "verified_rows": len(rows),
            },
            sort_keys=True,
        )
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--artifact",
        default="experiments/atlas-rank5-balanced-area.json",
    )
    parser.add_argument("--recompute-row", action="store_true")
    args = parser.parse_args()
    verify(args.artifact, args.recompute_row)


if __name__ == "__main__":
    main()
