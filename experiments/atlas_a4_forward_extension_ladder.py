#!/usr/bin/env python3
"""Classify the first exact extension beyond the 144-state forward fan.

The local fan uses first-chart ``r,z`` and the second-chart involution
``b_1=s_2 r_2``.  Adjoin the rest of the second-chart S3 and the opposite
oriented core edge from first-chart r to ``b_0=s_2``.  This is the smallest
packet enlargement that leaves the two-fan carrier while retaining one chart
direction.
"""

import json
from collections import Counter

from sympy.combinatorics.free_groups import free_group
from sympy.combinatorics.fp_groups import FpGroup


def main():
    free, r, z, t, s = free_group("r,z,t,s")
    group = FpGroup(free, [
        r**3,
        z**3,
        z*r*z**-1*r**-1,
        t**3,
        s**2,
        (s*t)**2,
        (r**-1*s*t)**3,
        (z*s*t)**3,
        (r*s)**3,
    ])
    order = group.order(strategy="coset_table_based")
    output = {
        "presentation": (
            "first <r,z>=C3^2, second <t,s>=S3, triangles "
            "(r^-1*s*t)^3,(z*s*t)^3,(r*s)^3"
        ),
        "order": int(order) if order != float("inf") else "infinity",
    }
    if order != float("inf"):
        permutation_group, isomorphism = group._to_perm_group()
        derived = permutation_group.derived_subgroup()
        output.update({
            "abelian_invariants": [
                int(value) for value in permutation_group.abelian_invariants()
            ],
            "center_order": int(permutation_group.center().order()),
            "derived_series_orders": [
                int(value.order()) for value in permutation_group.derived_series()
            ],
            "derived_element_order_histogram": {
                str(element_order): count
                for element_order, count in sorted(Counter(
                    int(element.order())
                    for element in derived.generate_schreier_sims()
                ).items())
            },
            "first_c3_square_order": int(permutation_group.subgroup([
                isomorphism(r), isomorphism(z)
            ]).order()),
            "second_s3_order": int(permutation_group.subgroup([
                isomorphism(t), isomorphism(s)
            ]).order()),
        })
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
