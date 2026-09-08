#!/usr/bin/env python3
"""Exact counterexamples to ordinary normalized-HS word-energy inequalities.

The candidate is e_word <= coefficient * sum(e_relator), in every matrix
dimension. A verified strict violation refutes that coefficient. Neither a
passed tuple nor a bounded search without a violation proves the inequality.
All matrix arithmetic uses Q(i), with no floating point or dependencies.
See research/artifacts/hs-word-certificate-rational-search.md.
"""

import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import count
import json
from pathlib import Path


def rational(value):
    if isinstance(value, bool) or not isinstance(value, (str, int)):
        raise ValueError("rational entries must be integers or rational strings")
    return Q(value)


@dataclass(frozen=True)
class Gaussian:
    re: Q = Q(0)
    im: Q = Q(0)

    def __add__(self, other):
        return Gaussian(self.re + other.re, self.im + other.im)

    def __neg__(self):
        return Gaussian(-self.re, -self.im)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        return Gaussian(self.re * other.re - self.im * other.im,
                        self.re * other.im + self.im * other.re)

    def __truediv__(self, other):
        norm = other.re ** 2 + other.im ** 2
        if not norm:
            raise ValueError("singular matrix")
        z = self * other.conjugate()
        return Gaussian(z.re / norm, z.im / norm)

    def conjugate(self):
        return Gaussian(self.re, -self.im)

    def encoded(self):
        return [str(self.re), str(self.im)]


ZERO, ONE = Gaussian(), Gaussian(Q(1))


def identity(d):
    return tuple(tuple(ONE if i == j else ZERO for j in range(d))
                 for i in range(d))


def adjoint(a):
    return tuple(tuple(a[j][i].conjugate() for j in range(len(a)))
                 for i in range(len(a)))


def multiply(a, b):
    d = len(a)
    return tuple(tuple(sum((a[i][k] * b[k][j] for k in range(d)), ZERO)
                       for j in range(d)) for i in range(d))


def inverse(a):
    d = len(a)
    rows = [list(row) + list(unit) for row, unit in zip(a, identity(d))]
    for col in range(d):
        pivot = next((j for j in range(col, d) if rows[j][col] != ZERO), None)
        if pivot is None:
            raise ValueError("singular matrix")
        rows[col], rows[pivot] = rows[pivot], rows[col]
        scale = rows[col][col]
        rows[col] = [z / scale for z in rows[col]]
        for j in range(d):
            if j != col:
                scale = rows[j][col]
                rows[j] = [x - scale * y for x, y in zip(rows[j], rows[col])]
    return tuple(tuple(row[d:]) for row in rows)


def cayley(parameters, d):
    """Cayley transform of a skew-Hermitian matrix with d^2 real parameters."""
    if len(parameters) != d * d:
        raise ValueError("wrong number of Cayley parameters")
    k = [[ZERO for _ in range(d)] for _ in range(d)]
    values = iter(parameters)
    for i in range(d):
        k[i][i] = Gaussian(Q(0), next(values))
    for i in range(d):
        for j in range(i + 1, d):
            k[i][j] = Gaussian(next(values), next(values))
            k[j][i] = -k[i][j].conjugate()
    unit = identity(d)
    plus = tuple(tuple(unit[i][j] + k[i][j] for j in range(d)) for i in range(d))
    minus = tuple(tuple(unit[i][j] - k[i][j] for j in range(d)) for i in range(d))
    return multiply(minus, inverse(plus))


def candidate(data):
    names = data.get("generators")
    if (not isinstance(names, list) or not names or
            not all(isinstance(s, str) and s for s in names) or
            len(set(names)) != len(names)):
        raise ValueError("generators must be distinct nonempty names")
    relators = data.get("relators")
    if not isinstance(relators, list):
        raise ValueError("relators must be a list of signed-index words")
    for word in [data.get("word")] + relators:
        if not isinstance(word, list) or not all(
                type(x) is int and 1 <= abs(x) <= len(names) for x in word):
            raise ValueError("words use nonzero signed generator indices")
    coefficient = rational(data.get("coefficient"))
    if coefficient <= 0:
        raise ValueError("coefficient must be positive")
    return {"generators": names, "relators": relators, "word": data["word"],
            "coefficient": str(coefficient)}


def decode_matrix(data):
    if not isinstance(data, list) or not data:
        raise ValueError("matrices must have positive dimension")
    d = len(data)
    if not all(isinstance(row, list) and len(row) == d for row in data):
        raise ValueError("matrix must be square")
    rows = []
    for row in data:
        values = []
        for z in row:
            if not isinstance(z, list) or len(z) != 2:
                raise ValueError("each Q(i) entry is [real, imaginary]")
            values.append(Gaussian(rational(z[0]), rational(z[1])))
        rows.append(tuple(values))
    return tuple(rows)


def encode_matrix(a):
    return [[z.encoded() for z in row] for row in a]


def evaluate(generators, word):
    out = identity(len(generators[0]))
    for letter in word:
        a = generators[abs(letter) - 1]
        out = multiply(out, a if letter > 0 else adjoint(a))
    return out


def energy(a):
    """Compute squared entry differences directly, with dimension normalization."""
    d = len(a)
    return sum(((a[i][j].re - int(i == j)) ** 2 + a[i][j].im ** 2
                for i in range(d) for j in range(d)), Q(0)) / d


def check(data, matrices):
    c = candidate(data)
    if len(matrices) != len(c["generators"]):
        raise ValueError("one matrix is required per generator")
    d = len(matrices[0])
    if not d or any(len(a) != d or any(len(row) != d for row in a) for a in matrices):
        raise ValueError("all matrices must have the same positive dimension")
    for a in matrices:
        if multiply(adjoint(a), a) != identity(d):
            raise ValueError("matrix is not exactly unitary")
    mark = energy(evaluate(matrices, c["word"]))
    relators = [energy(evaluate(matrices, w)) for w in c["relators"]]
    total = sum(relators, Q(0))
    margin = mark - rational(c["coefficient"]) * total
    return {"status": "counterexample" if margin > 0 else "no_violation_at_tuple",
            "dimension": d, "word_energy": str(mark),
            "relator_energies": [str(x) for x in relators],
            "relator_energy_sum": str(total), "strict_margin": str(margin),
            "proves_all_dimensions": False}


def integer_vectors(length, budget):
    """All integer vectors of l1 norm at most budget, in a finite traversal."""
    if not length:
        yield ()
        return

    def signed_values(remaining):
        yield 0
        for magnitude in range(1, remaining + 1):
            yield magnitude
            yield -magnitude

    # An explicit stack avoids an artificial Python recursion-depth bound
    # on the matrix dimensions covered by the mathematical enumeration.
    values = [0] * length
    stack = [(0, budget, signed_values(budget))]
    while stack:
        index, remaining, choices = stack[-1]
        try:
            value = next(choices)
        except StopIteration:
            stack.pop()
            continue
        values[index] = value
        if index + 1 == length:
            yield tuple(values)
        else:
            next_budget = remaining - abs(value)
            stack.append((index + 1, next_budget, signed_values(next_budget)))


def rational_tuples(generator_count, max_dimension=None, max_height=None):
    """Fair unbounded enumeration; optional bounds restrict its scope explicitly.

    At height h use d <= h, a common denominator <= h, and total integer
    numerator l1 norm <= h. Every finite rational skew-Hermitian tuple is
    eventually visited when both bounds are omitted.
    """
    heights = count(1) if max_height is None else range(1, max_height + 1)
    for height in heights:
        for d in range(1, min(height, max_dimension or height) + 1):
            width = d * d
            for denominator in range(1, height + 1):
                for integers in integer_vectors(generator_count * width, height):
                    parameters = [Q(n, denominator) for n in integers]
                    matrices = [cayley(parameters[j * width:(j + 1) * width], d)
                                for j in range(generator_count)]
                    yield matrices, {"height": height, "denominator": denominator,
                                     "integer_parameters": list(integers)}


def search(data, max_tests, max_dimension=None, max_height=None):
    c = candidate(data)
    tested = 0
    largest_dimension = 0
    for matrices, source in rational_tuples(len(c["generators"]), max_dimension, max_height):
        if tested >= max_tests:
            break
        tested += 1
        largest_dimension = max(largest_dimension, len(matrices[0]))
        result = check(c, matrices)
        if result["status"] == "counterexample":
            return {"format": "hs-word-counterexample-v1", "candidate": c,
                    "matrices": [encode_matrix(a) for a in matrices],
                    "verification": result, "search_parameters": source,
                    "tuples_tested": tested}
    return {"status": "inconclusive", "candidate": c, "tuples_tested": tested,
            "largest_dimension_tested": largest_dimension,
            "bounds": {"max_tests": max_tests, "max_dimension": max_dimension,
                       "max_height": max_height}, "proves_all_dimensions": False}


def positive_int(text):
    value = int(text)
    if value <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    verify = sub.add_parser("verify", help="recompute an explicit rational matrix witness")
    verify.add_argument("file", type=Path)
    scan = sub.add_parser("search", help="bounded exact search; no success is inconclusive")
    scan.add_argument("file", type=Path)
    scan.add_argument("--max-tests", type=positive_int, default=1000)
    scan.add_argument("--max-dimension", type=positive_int)
    scan.add_argument("--max-height", type=positive_int)
    args = parser.parse_args()
    try:
        data = json.loads(args.file.read_text())
        if args.command == "verify":
            if data.get("format") != "hs-word-counterexample-v1":
                raise ValueError("unsupported witness format")
            result = check(data["candidate"], [decode_matrix(a) for a in data["matrices"]])
        else:
            result = search(data, args.max_tests, args.max_dimension, args.max_height)
        print(json.dumps(result, indent=2))
        status = result.get("status", result.get("verification", {}).get("status"))
        return 0 if status == "counterexample" else 2
    except (ValueError, KeyError, TypeError, AttributeError, ZeroDivisionError, OSError) as error:
        print(json.dumps({"status": "invalid_input", "error": str(error)}))
        return 64


if __name__ == "__main__":
    raise SystemExit(main())
