#!/usr/bin/env python3
"""Exact Sage/GAP check of the BS(1,4)+involution quotient by s^p.

The conjectural quotient is PSL(2,p).  This bounded script computes the order
of the finitely presented quotient for one small odd prime.  It is a
falsification check for the proposed classification argument, not a proof for
all p.
"""

import argparse
import json

from sage.all import FreeGroup


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--p", type=int, required=True)
    parser.add_argument("--output")
    args = parser.parse_args()

    free = FreeGroup(names=("x", "r", "s"))
    x, r, s = free.gens()
    relators = (
        x**2,
        (x * r) ** 2,
        (x * s**2) ** 3,
        (x * r * s) ** 3,
        r * s * r**-1 * s**-4,
        s**args.p,
    )
    quotient = free / relators
    order = int(quotient.order())
    expected = args.p * (args.p * args.p - 1) // 2
    payload = {
        "p": args.p,
        "computed_order": order,
        "expected_psl2_order": expected,
        "matches": order == expected,
        "status": "finite-p check only; not a uniform presentation proof",
    }
    rendered = json.dumps(payload, indent=2, sort_keys=True)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as handle:
            handle.write(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()
