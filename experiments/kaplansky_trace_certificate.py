#!/usr/bin/env python3
"""Exact, finite-precision lifted-trace obstruction certificates.

This does not decide Kaplansky's conjecture. An unequal lifted trace excludes
projective equivalence; an equal trace is inconclusive. The CLI accepts a
validated finite group table and square matrix idempotents, or replays the
built-in examples. See research/finite-precision-lifted-trace-obstruction.md.

Examples:
    python experiments/kaplansky_trace_certificate.py --examples
    python experiments/kaplansky_trace_certificate.py --input candidate.json
    python experiments/kaplansky_trace_certificate.py --verify certificates.json
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import permutations, product
import json
from math import isqrt
from pathlib import Path


Matrix = dict[tuple[int, int, int], int]


def positive_integer(value: object, label: str) -> int:
    if type(value) is not int or value < 1:
        raise ValueError(f"{label} must be a positive integer")
    return value


def prime(value: object) -> int:
    p = positive_integer(value, "p")
    if p < 2 or any(p % d == 0 for d in range(2, isqrt(p) + 1)):
        raise ValueError("p must be prime")
    return p


def reduced(a: Matrix, modulus: int) -> Matrix:
    return {key: value % modulus for key, value in a.items() if value % modulus}


class FiniteGroup:
    """A table is accepted only after the group axioms have been checked."""

    def __init__(self, table: list[list[int]], identity: int = 0):
        if not isinstance(table, list) or not table:
            raise ValueError("group table must be a nonempty list")
        self.order = len(table)
        if type(identity) is not int or not 0 <= identity < self.order:
            raise ValueError("invalid group identity index")
        for row in table:
            if not isinstance(row, list) or len(row) != self.order:
                raise ValueError("group table must be square")
            if any(type(x) is not int or not 0 <= x < self.order for x in row):
                raise ValueError("group table has an invalid element index")
        self.table = tuple(tuple(row) for row in table)
        self.identity = identity
        t, size = self.table, self.order
        for a in range(size):
            if t[identity][a] != a or t[a][identity] != a:
                raise ValueError("table identity law fails")
            if not any(t[a][b] == identity == t[b][a] for b in range(size)):
                raise ValueError("table inverse law fails")
        for a, b, c in product(range(size), repeat=3):
            if t[t[a][b]][c] != t[a][t[b][c]]:
                raise ValueError("table associativity fails")


class MatrixGroupRing:
    def __init__(self, group: FiniteGroup, p: int, precision: int, size: int):
        self.group = group
        self.p = prime(p)
        self.precision = positive_integer(precision, "precision")
        self.size = positive_integer(size, "matrix_size")
        self.modulus = p ** precision

    def from_terms(self, terms: list[list[int]]) -> Matrix:
        if not isinstance(terms, list):
            raise ValueError("matrix terms must be a list")
        out: Matrix = {}
        for term in terms:
            if not isinstance(term, list) or len(term) != 4:
                raise ValueError("a matrix term must be [row, column, group, coefficient]")
            if any(type(x) is not int for x in term):
                raise ValueError("matrix term entries must be integers")
            i, j, g, coefficient = term
            if not (0 <= i < self.size and 0 <= j < self.size
                    and 0 <= g < self.group.order):
                raise ValueError("matrix term index out of bounds")
            key = (i, j, g)
            out[key] = out.get(key, 0) + coefficient
        return reduced(out, self.modulus)

    def identity(self) -> Matrix:
        return {(i, i, self.group.identity): 1 for i in range(self.size)}

    def add(self, *matrices: Matrix) -> Matrix:
        out: Matrix = {}
        for matrix in matrices:
            for key, value in matrix.items():
                out[key] = out.get(key, 0) + value
        return reduced(out, self.modulus)

    def scale(self, scalar: int, matrix: Matrix) -> Matrix:
        return reduced({key: scalar * value for key, value in matrix.items()}, self.modulus)

    def mul(self, a: Matrix, b: Matrix) -> Matrix:
        out: Matrix = {}
        for (i, j, g), x in a.items():
            for (j2, k, h), y in b.items():
                if j == j2:
                    key = (i, k, self.group.table[g][h])
                    out[key] = out.get(key, 0) + x * y
        return reduced(out, self.modulus)

    def trace(self, a: Matrix) -> int:
        return sum(a.get((i, i, self.group.identity), 0)
                   for i in range(self.size)) % self.modulus

    def lift(self, a: Matrix) -> tuple[Matrix, int]:
        """Accept any coefficient lift; reject a nonidempotent reduction."""
        a = reduced(a, self.modulus)
        original = reduced(a, self.p)
        if reduced(self.mul(a, a), self.p) != original:
            raise ValueError("input is not idempotent modulo p")
        guaranteed, rounds = 1, 0
        while guaranteed < self.precision:
            square = self.mul(a, a)
            a = self.add(self.scale(3, square), self.scale(-2, self.mul(square, a)))
            guaranteed *= 2
            rounds += 1
            defect = self.add(self.mul(a, a), self.scale(-1, a))
            if reduced(defect, self.p ** min(guaranteed, self.precision)):
                raise ArithmeticError("polynomial lift failed its defect bound")
        if self.mul(a, a) != a or reduced(a, self.p) != original:
            raise ArithmeticError("lift failed exact idempotence or reduction")
        return a, rounds

    def regular_rank(self, a: Matrix) -> int:
        """Independent check via the full regular action and field elimination."""
        order, p = self.group.order, self.p
        dim = self.size * order
        rows = [[0] * dim for _ in range(dim)]
        for (i, j, g), coefficient in a.items():
            for h in range(order):
                row, column = i * order + self.group.table[g][h], j * order + h
                rows[row][column] = (rows[row][column] + coefficient) % p
        rank = 0
        for column in range(dim):
            pivot = next((i for i in range(rank, dim) if rows[i][column]), None)
            if pivot is None:
                continue
            rows[rank], rows[pivot] = rows[pivot], rows[rank]
            inverse = pow(rows[rank][column], -1, p)
            rows[rank] = [(x * inverse) % p for x in rows[rank]]
            for i in range(rank + 1, dim):
                scalar = rows[i][column]
                if scalar:
                    rows[i] = [(x - scalar * y) % p
                               for x, y in zip(rows[i], rows[rank])]
            rank += 1
        return rank


def terms(a: Matrix) -> list[list[int]]:
    return [[*key, a[key]] for key in sorted(a)]


def detection_precision(p: int, size: int, order: int) -> int:
    p = prime(p)
    size = positive_integer(size, "matrix_size")
    order = positive_integer(order, "group order")
    while order % p == 0:
        order //= p
    bound, k = size * order, 1
    while p ** k <= bound:
        k += 1
    return k


def certify(spec: dict) -> dict:
    """Return a replayable certificate, never a positive equivalence claim."""
    group = FiniteGroup(spec["group"]["table"], spec["group"].get("identity", 0))
    ring = MatrixGroupRing(group, spec["p"], spec["precision"], spec["matrix_size"])
    inputs = {key: ring.from_terms(spec[key]) for key in ("e", "f")}
    certificates = {}
    for key, a in inputs.items():
        lifted, rounds = ring.lift(a)
        rank = ring.regular_rank(a)
        expected = Fraction(rank, group.order)
        if expected.denominator % ring.p == 0:
            raise ArithmeticError("regular rank contradicts p-adic integrality")
        expected_residue = (expected.numerator
                            * pow(expected.denominator, -1, ring.modulus)) % ring.modulus
        trace = ring.trace(lifted)
        if trace != expected_residue:
            raise ArithmeticError("lift trace disagrees with independent regular rank")
        certificates[key] = {
            "lift": terms(lifted), "rounds": rounds, "trace": trace,
            "regular_rank": rank,
            "normalized_rank": [expected.numerator, expected.denominator],
        }
    e, f = (reduced(inputs[key], ring.p) for key in ("e", "f"))
    nested = (e != f and reduced(ring.mul(e, f), ring.p) == f
              and reduced(ring.mul(f, e), ring.p) == f)
    difference = (certificates["e"]["trace"] - certificates["f"]["trace"]) % ring.modulus
    bound = detection_precision(ring.p, ring.size, group.order) if nested else None
    if nested and ring.precision >= bound and difference == 0:
        raise ArithmeticError("strict nesting contradicts the detection bound")
    return {
        "input": spec, "modulus": ring.modulus, **certificates,
        "trace_difference": difference,
        "status": "obstructed" if difference else "inconclusive",
        "strictly_nested": nested,
        "sufficient_nested_detection_precision": bound,
    }


def cyclic_table(order: int) -> list[list[int]]:
    return [[(i + j) % order for j in range(order)] for i in range(order)]


def example_specs() -> list[dict]:
    def spec(name, table, p, k, e, f, size=1):
        return {"name": name, "group": {"table": table, "identity": 0},
                "p": p, "precision": k, "matrix_size": size, "e": e, "f": f}

    out = []
    # Coordinates (i,j) in C3 x C3 have index 3*i+j. They model g and h
    # in the existing Leavitt node, whose proof supplies the embedding in Q.
    pairs = list(product(range(3), repeat=2))
    table = [[pairs.index(((a + c) % 3, (b + d) % 3))
              for c, d in pairs] for a, b in pairs]
    e = [[0, 0, g, 1] for g in (3, 6)]
    f = [[0, 0, g, 1] for g in (4, 5, 7, 8)]
    for k in (1, 2, 5):
        out.append(spec(f"leavitt_c3xc3_precision_{k}", table, 2, k, e, f))
    # Scalar examples that defeat every precision <= r, then separate at r+1.
    for p, r in ((2, 1), (2, 2), (2, 3), (3, 1), (3, 2)):
        order = p ** r + 1
        inverse = pow(order, -1, p)
        a = [[0, 0, g, ((g == 0) - inverse) % p] for g in range(order)]
        for k in (r, r + 1):
            out.append(spec(f"cyclic_p{p}_r{r}_precision_{k}",
                            cyclic_table(order), p, k, a, []))
    # Noncommutative group arithmetic: conjugate averaging idempotents.
    perms = list(permutations(range(3)))
    table = [[perms.index(tuple(a[b[i]] for i in range(3)))
              for b in perms] for a in perms]
    a, b = perms.index((1, 0, 2)), perms.index((0, 2, 1))
    out.append(spec("s3_conjugate_averages", table, 3, 3,
                    [[0, 0, 0, 2], [0, 0, a, 2]],
                    [[0, 0, 0, 2], [0, 0, b, 2]]))
    # Equal trace does not imply equivalence, already for the two C2 characters.
    out.append(spec("c2_distinct_characters_equal_trace", cyclic_table(2), 3, 3,
                    [[0, 0, 0, 2], [0, 0, 1, 2]],
                    [[0, 0, 0, 2], [0, 0, 1, 1]]))
    # Matrix trace can vanish at low precision even for a nonzero identity.
    for k in (2, 3):
        out.append(spec(f"matrix_identity_precision_{k}", [[0]], 2, k,
                        [[i, i, 0, 1] for i in range(4)], [], size=4))
    return out


def bundle(specs: list[dict]) -> dict:
    return {
        "schema": 1,
        "scope": ("Unequal residues obstruct projective equivalence in every group "
                  "algebra containing the input group as a subgroup. Equal residues "
                  "are inconclusive. This file does not certify an embedding in Q "
                  "or a solution of Kaplansky's conjecture."),
        "cases": [certify(spec) for spec in specs],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--examples", action="store_true")
    source.add_argument("--input", type=Path)
    source.add_argument("--verify", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        if args.verify:
            supplied = json.loads(args.verify.read_text())
            replayed = bundle([case["input"] for case in supplied["cases"]])
            if supplied != replayed:
                raise ValueError("certificate differs from exact replay")
            print(f"Verified {len(replayed['cases'])} exact trace certificates.")
            return
        specs = example_specs() if args.examples else [json.loads(args.input.read_text())]
        result = json.dumps(bundle(specs), indent=2, sort_keys=True) + "\n"
        if args.output:
            args.output.write_text(result)
        else:
            print(result, end="")
    except (ValueError, KeyError, TypeError, ArithmeticError, OSError) as exc:
        parser.exit(2, f"error: {exc}\n")


if __name__ == "__main__":
    main()
