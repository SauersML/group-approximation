#!/usr/bin/env python3
"""Classify the shared forward fan after adjoining collision 19243.

The first chart contributes commuting ``r,z`` and the collision involution c,
which centralizes r and inverts z.  The second chart contributes
``<t,s>=S3``.  The adjacent core and forward contexts use the common second
involution ``s*t``; the final relator is the exact S3-relative collision word.
"""

import argparse
import json
from collections import Counter

from sympy.combinatorics.free_groups import free_group
from sympy.combinatorics.fp_groups import FpGroup


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--impose-collision", action="store_true")
    args = parser.parse_args()
    free, r, z, c, t, s = free_group("r,z,c,t,s")
    collision = t*c*s*c*t**-1*c*s*t*c
    relations = [
        r**3,
        z**3,
        z*r*z**-1*r**-1,
        c**2,
        c*r*c*r**-1,
        c*z*c*z,
        t**3,
        s**2,
        (s*t)**2,
        (r**-1*s*t)**3,
        (z*s*t)**3,
    ]
    if args.impose_collision:
        relations.append(collision)
    group = FpGroup(free, relations)
    order = group.order(strategy="coset_table_based")
    output = {
        "presentation": (
            "first <r,z,c> with [r,z]=[r,c]=1 and c z c=z^-1; "
            "second <t,s>=S3; core (r^-1*s*t)^3; forward (z*s*t)^3; "
            "collision t*c*s*c*t^-1*c*s*t*c"
        ),
        "collision_imposed": args.impose_collision,
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
            "first_support_order": int(permutation_group.subgroup([
                isomorphism(r), isomorphism(z), isomorphism(c)
            ]).order()),
            "second_s3_order": int(permutation_group.subgroup([
                isomorphism(t), isomorphism(s)
            ]).order()),
        })
        if not args.impose_collision:
            collision_image = isomorphism(collision)
            collision_normal_closure = permutation_group.normal_closure([collision_image])
            output.update({
                "collision_order": int(collision_image.order()),
                "collision_normal_closure_order": int(collision_normal_closure.order()),
                "collision_normal_closure_contains_first_c": collision_normal_closure.contains(
                    isomorphism(c)
                ),
                "collision_normal_closure_contains_second_b1": collision_normal_closure.contains(
                    isomorphism(s*t)
                ),
                "collision_quotient_order": int(
                    permutation_group.order() // collision_normal_closure.order()
                ),
            })
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
