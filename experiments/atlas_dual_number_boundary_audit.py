"""Audit the dual-number central quotient on all 234 boundary relations.

The certified quotient kills 178 perfect-overlap relations and sends phase
class 11 to its unique central involution.  This exact audit classifies every
shortest remaining relation and groups the 56 survivors by free-product
conjugacy and inversion.
"""

import json

from atlas_certified_a8_alignment import boundary_words
from atlas_certified_dual_number_certificate import (
    chart_images,
    evaluate,
    natural_a8_map,
    pair_equal,
)
from atlas_survivor_conjugacy import unoriented_key


SURVIVOR_REPRESENTATIVES = (11, 30, 44, 55)


def main():
    images = natural_a8_map()
    first, second, identity, zero, _tangent = chart_images(images)
    words = boundary_words()
    identity_pair = (identity, zero)
    central_phase = (identity, identity)

    labels = []
    for word in words:
        value = evaluate(word, first, second, identity, zero)
        if pair_equal(value, identity_pair):
            labels.append("identity")
        elif pair_equal(value, central_phase):
            labels.append("central_involution")
        else:
            labels.append("noncentral")

    representative_by_key = {
        unoriented_key(words[index]): index
        for index in SURVIVOR_REPRESENTATIVES
    }
    classes = {index: [] for index in SURVIVOR_REPRESENTATIVES}
    for index, label in enumerate(labels):
        if label == "identity":
            continue
        key = unoriented_key(words[index])
        if key not in representative_by_key:
            raise AssertionError("nonidentity word left the four survivor classes")
        classes[representative_by_key[key]].append(index)

    records = []
    for representative in SURVIVOR_REPRESENTATIVES:
        members = classes[representative]
        outcomes = {labels[index] for index in members}
        if len(members) != 14 or len(outcomes) != 1:
            raise AssertionError("survivor class is not uniform of size fourteen")
        records.append({
            "representative": representative,
            "outcome": outcomes.pop(),
            "members": members,
        })

    counts = {label: labels.count(label) for label in (
        "identity", "central_involution", "noncentral")}
    if counts != {
            "identity": 178,
            "central_involution": 28,
            "noncentral": 28}:
        raise AssertionError("unexpected complete-boundary classification")

    print(json.dumps({
        "boundary_words": len(words),
        "counts": counts,
        "survivor_classes": records,
    }, indent=2))


if __name__ == "__main__":
    main()
