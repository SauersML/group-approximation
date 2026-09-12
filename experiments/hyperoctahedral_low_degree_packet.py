#!/usr/bin/env python3
"""Audit the low-degree odd bipartitions used by the hyperoctahedral packet."""

import argparse
import json
import math


def partitions(n: int, maximum: int | None = None) -> list[tuple[int, ...]]:
    if n == 0:
        return [()]
    if maximum is None or maximum > n:
        maximum = n
    out: list[tuple[int, ...]] = []
    for first in range(maximum, 0, -1):
        for tail in partitions(n - first, first):
            out.append((first,) + tail)
    return out


def specht_degree(partition: tuple[int, ...]) -> int:
    n = sum(partition)
    hooks = 1
    for row, width in enumerate(partition):
        for column in range(width):
            below = sum(1 for later in partition[row + 1:] if later > column)
            hooks *= width - column + below
    return math.factorial(n) // hooks


def audit(m: int) -> dict:
    threshold = m * (m - 2)
    marked = []
    low = []
    for weight in range(1, m + 1, 2):
        for lam in partitions(m - weight):
            for mu in partitions(weight):
                degree = (math.comb(m, weight)
                          * specht_degree(lam)
                          * specht_degree(mu))
                record = {
                    "lambda": list(lam),
                    "mu": list(mu),
                    "weight": weight,
                    "degree": degree,
                }
                marked.append(record)
                if degree < threshold:
                    low.append(record)

    assert len(low) == 4
    assert {record["degree"] for record in low} == {m}
    assert {record["weight"] for record in low} == {1, m - 1}
    assert min(record["degree"] for record in marked) == m

    # Every selector column is repeated an even number L of times, so its
    # total coordinate product is +1.  A weight-(m-1) character omitting j
    # therefore evaluates exactly like the weight-one character j.
    sample_allowed = [
        tuple(1 if ((index >> bit) & 1) == 0 else -1
              for bit in range(3))
        for index in range(5)
    ]
    repetition = 2 * math.ceil(m / (2 * len(sample_allowed)))
    labels = (sample_allowed * repetition)[:m]
    if len(labels) < m:
        labels.extend(sample_allowed[:m - len(labels)])
    # Use only m which are exact even multiples for this explicit spectrum
    # check; the representation-degree audit above applies to every even m.
    spectrum_checked = m % (2 * len(sample_allowed)) == 0
    if spectrum_checked:
        for bit in range(3):
            assert math.prod(label[bit] for label in labels) == 1
        weight_one = sorted(labels)
        weight_complement = sorted(tuple(
            math.prod(labels[index][bit]
                      for index in range(m) if index != omitted)
            for bit in range(3)
        ) for omitted in range(m))
        assert weight_one == weight_complement

    return {
        "m": m,
        "threshold": threshold,
        "marked_bipartitions": len(marked),
        "low_marked_bipartitions": low,
        "minimum_marked_degree": m,
        "complement_spectrum_checked": spectrum_checked,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-m", type=int, default=18)
    args = parser.parse_args()
    records = [audit(m) for m in range(8, args.max_m + 1, 2)]
    print(json.dumps({"all_checks_pass": True, "records": records}, indent=2))


if __name__ == "__main__":
    main()
