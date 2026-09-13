#!/usr/bin/env python3
"""Exact finite-period replay of the binary entropy/traffic countermodel.

Run only through the authorized MSI wrapper. The written artifact proves
all periods; this replay checks the stated finite construction and arithmetic.
"""
from fractions import Fraction
import json


def verify_period(q):
    assert q >= 4 and q & (q - 1) == 0
    traffic = {1: [0] * q, 2: [0] * q}
    lengths = []
    for r in range(q):
        if r % 2 == 0:
            path = list(range(r, -1, -2)) + list(range(1, r + 2, 2))
        else:
            path = list(range(r, 0, -2)) + list(range(0, r + 2, 2))
        assert path[0] == r and path[-1] == r + 1
        lengths.append(len(path) - 1)
        for a, b in zip(path, path[1:]):
            label, start = abs(b - a), min(a, b) % q
            assert label in (1, 2)
            assert (label == 1 and start == 0) or (label == 2 and start != q - 1)
            traffic[label][start] += 1
    assert traffic[1] == [q] + [0] * (q - 1)
    expected = [q - r - 1 for r in range(q)]
    # Formula (4) simplifies to q-r-1 for both residue parities.
    assert traffic[2] == expected
    assert max(lengths) == q
    p = {j: Fraction(sum(k > 0 for k in traffic[j]), q) for j in traffic}
    m = {j: Fraction(sum(traffic[j]), q) for j in traffic}
    budget = sum(p.values())
    defect = sum(min(1, m[j]) - p[j] for j in traffic)
    flags = {j: Fraction(sum(k >= 2 for k in traffic[j]), q) for j in traffic}
    assert budget == 1 and defect == 1
    assert flags == {1: Fraction(1, q), 2: Fraction(q - 2, q)}
    return {"period": q, "budget": str(budget), "defect": str(defect),
            "max_path_length": max(lengths),
            "reuse_probabilities": {str(j): str(v) for j, v in flags.items()}}


def main():
    rows = [verify_period(2 ** n) for n in range(2, 10)]
    print(json.dumps({"scope": "finite exact replay, not infinite theorem verification",
                      "periods": rows}, indent=2))


if __name__ == "__main__":
    main()
