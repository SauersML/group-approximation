#!/usr/bin/env python3
"""Search low-index finite quotients of the forward-fan collision quotient.

The presentation is the one-relator quotient of the virtually free graph
``(C3 x S3) *_(C3^2) (C2^4 : C3^2) *_C2 S3``.  Each low-index subgroup gives
a finite permutation quotient.  We test survival of the common involution b
and faithful images of all three finite vertex groups.
"""

import argparse
import json
from collections import Counter

from sympy.combinatorics import Permutation, PermutationGroup
from sympy.combinatorics.free_groups import free_group
from sympy.combinatorics.fp_groups import FpGroup, low_index_subgroups


def presentation():
    free, r, z, c, t, s = free_group("r,z,c,t,s")
    collision = t*c*s*c*t**-1*c*s*t*c
    group = FpGroup(free, [
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
        collision,
    ])
    return group, (r, z, c, t, s)


def quotient_from_table(group, table):
    generators = group.generators
    images = [
        Permutation([table.table[row][2*index] for row in range(len(table.table))])
        for index, _generator in enumerate(generators)
    ]
    return PermutationGroup(images), dict(zip(generators, images))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-index", type=int, default=16)
    args = parser.parse_args()

    group, (r, z, c, t, s) = presentation()
    tables = low_index_subgroups(group, args.max_index)
    records = []
    for table in tables:
        quotient, image = quotient_from_table(group, table)
        b = image[s] * image[t]
        central_carrier = quotient.subgroup([image[r], image[z], b])
        first_support = quotient.subgroup([image[r], image[z], image[c]])
        second_support = quotient.subgroup([image[t], image[s]])
        records.append({
            "degree": len(table.table),
            "quotient_order": int(quotient.order()),
            "b_order": int(b.order()),
            "central_carrier_order": int(central_carrier.order()),
            "first_support_order": int(first_support.order()),
            "second_support_order": int(second_support.order()),
        })

    records.sort(key=lambda record: (
        record["b_order"] != 2,
        record["central_carrier_order"] != 144,
        record["degree"],
        record["quotient_order"],
    ))
    faithful = [
        record for record in records
        if (
            record["central_carrier_order"] == 144
            and record["first_support_order"] == 18
            and record["second_support_order"] == 6
        )
    ]
    print(json.dumps({
        "b_survival_count": sum(record["b_order"] == 2 for record in records),
        "degree_histogram": dict(sorted(Counter(
            record["degree"] for record in records
        ).items())),
        "faithful_vertex_quotients": faithful,
        "low_index_subgroups": len(records),
        "max_index": args.max_index,
        "top_records": records[:20],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
