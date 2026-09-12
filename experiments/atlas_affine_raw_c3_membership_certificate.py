"""Certify whether the raw S3 three-cycle fixes the archived affine vector.

This is a lightweight verifier over already archived data.  It does not
rebuild the 20,005-dimensional left-ideal basis.  The JSON artifact
``atlas-boundary-f2-bridge-ideal.json`` stores four exact dual functionals
annihilating that ideal.  Pairing any one of them nontrivially with
``1+h_a h_b`` certifies that the three-cycle is not in the stabilizer of
``m=1+I``.
"""

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from atlas_asc_packet_build import raw_s3_letters  # noqa: E402
from atlas_boundary_group_algebra_audit import matrix_from_key  # noqa: E402
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX  # noqa: E402
from atlas_boundary_inner_alignment import enumerate_gl4  # noqa: E402
from atlas_two_chart_search import (I4, gf2_inv, gf2_mul,  # noqa: E402
                                    matrix_key)


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    artifact_path = os.path.join(
        here, "atlas-boundary-f2-bridge-ideal.json")
    with open(artifact_path, "r", encoding="utf-8") as stream:
        artifact = json.load(stream)

    if artifact["left_ideal_rank"] != 20005:
        raise AssertionError("archived ideal rank changed")
    if artifact["queue_remaining"] != 0:
        raise AssertionError("archived ideal closure is incomplete")

    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    letters, _raw = raw_s3_letters(alignment, gf2_inv(alignment))
    h_a, h_b = letters
    three_cycle = gf2_mul(h_a, h_b)

    elements = list(enumerate_gl4())
    index_by_key = {matrix_key(element): index
                    for index, element in enumerate(elements)}
    identity_index = index_by_key[matrix_key(I4)]
    cycle_index = index_by_key[matrix_key(three_cycle)]

    pairings = []
    for witness_id, support_list in enumerate(
            artifact["dual_witness_supports"]):
        support = set(support_list)
        identity_bit = int(identity_index in support)
        cycle_bit = int(cycle_index in support)
        pairings.append({
            "witness_id": witness_id,
            "support_size": len(support),
            "identity_bit": identity_bit,
            "three_cycle_bit": cycle_bit,
            "pairing_with_1_plus_cycle": identity_bit ^ cycle_bit,
        })

    detecting = [entry for entry in pairings
                 if entry["pairing_with_1_plus_cycle"] == 1]
    report = {
        "artifact": os.path.basename(artifact_path),
        "artifact_left_ideal_rank": artifact["left_ideal_rank"],
        "artifact_queue_remaining": artifact["queue_remaining"],
        "alignment_hex": INNER_ALIGNMENT_HEX,
        "raw_s3_letter_hex": [matrix_key(h).hex() for h in letters],
        "three_cycle_hex": matrix_key(three_cycle).hex(),
        "identity_index": identity_index,
        "three_cycle_index": cycle_index,
        "dual_pairings": pairings,
        "detecting_witness_ids": [entry["witness_id"]
                                  for entry in detecting],
        "one_plus_three_cycle_not_in_ideal": bool(detecting),
    }
    print(json.dumps(report, indent=2, sort_keys=True))
    if not detecting:
        raise SystemExit(
            "archived dual witnesses do not decide this membership")


if __name__ == "__main__":
    main()
