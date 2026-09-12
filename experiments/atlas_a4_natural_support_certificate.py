#!/usr/bin/env python3
"""Exact class and generation certificate for the natural A8 support fence."""

import json

from atlas_a4_19243_component_localization import (
    H18_LABELS,
    H6_LABELS,
    mul,
    order,
    subgroup,
)
from atlas_boundary_inner_alignment import enumerate_gl4


def main():
    labels = H6_LABELS + H18_LABELS
    involutions = [value for value in labels if order(value) == 2]
    order_threes = [value for value in labels if order(value) == 3]
    ambient = [tuple(map(tuple, value.tolist())) for value in enumerate_gl4()]

    involution_centralizers = sorted({
        sum(mul(value, g) == mul(g, value) for g in ambient)
        for value in involutions
    })
    order_three_centralizers = sorted({
        sum(mul(value, g) == mul(g, value) for g in ambient)
        for value in order_threes
    })
    order_three_closure = subgroup(order_threes)

    assert len(involutions) == 4
    assert len(order_threes) == 6
    assert involution_centralizers == [192]
    assert order_three_centralizers == [18]
    assert len(order_three_closure) == 20160

    print(json.dumps({
        "packet_involutions": len(involutions),
        "packet_order_three_letters": len(order_threes),
        "ambient_involution_centralizer_sizes": involution_centralizers,
        "ambient_order_three_centralizer_sizes": order_three_centralizers,
        "order_three_generated_subgroup_size": len(order_three_closure),
    }, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
