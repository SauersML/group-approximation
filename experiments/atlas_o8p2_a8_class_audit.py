#!/usr/bin/env python3
"""Exact recorded character-table audit of A8-bearing maximals of O8+(2)."""

import json

def main():
    # CTblLib's O8+(2) table records three triality classes of each of the
    # first three structures.  The remaining maximal structures have orders
    # not divisible by |A8|; their exact orders are included to make the
    # Lagrange filter replayable without CTblLib installed.
    structures = [
        ("S6(2)", 1451520, 3),
        ("2^6:A8", 1290240, 3),
        ("A9", 181440, 3),
        ("(3xU4(2)):2", 155520, 3),
        ("2^(1+8)+:(S3xS3xS3)", 110592, 1),
        ("3^4:2^3:S4", 15552, 1),
        ("(A5xA5):2^2", 14400, 3),
    ]
    ambient_order = 174182400
    records = [
        {
            "structure": structure,
            "order": order,
            "index": ambient_order // order,
            "conjugacy_classes": classes,
            "order_divisible_by_A8": order % 20160 == 0,
        }
        for structure, order, classes in structures
    ]
    carriers = [record for record in records if record["order_divisible_by_A8"]]
    if [(row["structure"], row["index"], row["conjugacy_classes"]) for row in carriers] != [
        ("S6(2)", 120, 3), ("2^6:A8", 135, 3), ("A9", 960, 3)
    ]:
        raise AssertionError("O8+(2) A8-bearing maximal carrier list changed")
    print(json.dumps({
        "source": "GAP CTblLib O8+(2) character-table information",
        "ambient": "O8+(2)",
        "ambient_order": ambient_order,
        "ambient_index_over_A8": ambient_order // 20160,
        "maximal_subgroups": records,
        "A8_order_divisible_maximals": carriers,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
