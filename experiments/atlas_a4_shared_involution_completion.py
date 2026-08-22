#!/usr/bin/env python3
"""Probe the universal completion of two A4 triangles sharing an involution.

The first-chart order-three labels r and z commute.  A core context and one
forward central-C3 context put the same transported involution b in an A4
triangle with each.  The resulting presentation is small enough for exact
Todd--Coxeter and low-index subgroup probes on MSI.
"""

import json
from collections import Counter

from sympy.combinatorics.free_groups import free_group
from sympy.combinatorics.fp_groups import FpGroup


def main():
    free, r, z, b = free_group("r,z,b")
    group = FpGroup(free, [
        r**3,
        z**3,
        b**2,
        r*z*r**-1*z**-1,
        (r*b)**3,
        (z*b)**3,
    ])
    order = group.order(strategy="coset_table_based")
    permutation_group, isomorphism = group._to_perm_group()
    r_image = isomorphism(r)
    z_image = isomorphism(z)
    b_image = isomorphism(b)
    derived_orders = [int(value.order()) for value in permutation_group.derived_series()]
    composition_orders = [int(value.order()) for value in permutation_group.composition_series()]
    derived = permutation_group.derived_subgroup()
    derived_elements = list(derived.generate_schreier_sims())
    order_three_subgroup = permutation_group.subgroup([r_image, z_image])
    conjugacy_orbit = {
        element**-1 * b_image * element
        for element in order_three_subgroup.generate_schreier_sims()
    }
    print(json.dumps({
        "abelian_invariants": [int(value) for value in permutation_group.abelian_invariants()],
        "center_order": int(permutation_group.center().order()),
        "composition_series_orders": composition_orders,
        "derived_series_orders": derived_orders,
        "derived_element_order_histogram": {
            str(order): count
            for order, count in sorted(Counter(
                int(element.order()) for element in derived_elements
            ).items())
        },
        "presentation": "<r,z,b | r^3,z^3,b^2,[r,z],(rb)^3,(zb)^3>",
        "order": int(order) if order != float("inf") else "infinity",
        "rz_subgroup_order": int(permutation_group.subgroup([r_image, z_image]).order()),
        "rz_conjugacy_orbit_of_b": len(conjugacy_orbit),
        "rb_subgroup_order": int(permutation_group.subgroup([r_image, b_image]).order()),
        "zb_subgroup_order": int(permutation_group.subgroup([z_image, b_image]).order()),
        "generator_orders": [int(r_image.order()), int(z_image.order()), int(b_image.order())],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
