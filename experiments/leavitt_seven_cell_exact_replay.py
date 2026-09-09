"""Exact seven-cell constants and Thompson replay; run on MSI after review.

Standard library only, ten-second internal budget, no search or completion
candidate. Products act on the left: (f*g)(x)=f(g(x)). Output is exclusive.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import time


class Prefix:
    deadline = float("inf")
    products = 0
    max_rows = 0
    row_cap = 512

    def __init__(self, rows):
        rows = list(rows)
        if len(rows) > Prefix.row_cap:
            raise ArithmeticError("512-row prefix table cap exceeded")
        Prefix.max_rows = max(Prefix.max_rows, len(rows))
        data = dict(rows)
        if len(rows) != len(data):
            raise ValueError("Repeated source prefix")
        while True:
            if time.monotonic() > Prefix.deadline:
                raise TimeoutError("Ten-second exact replay budget exceeded")
            for source, target in sorted(data.items()):
                if source.endswith("0") and target.endswith("0"):
                    sibling = source[:-1] + "1"
                    if data.get(sibling) == target[:-1] + "1":
                        del data[source], data[sibling]
                        data[source[:-1]] = target[:-1]
                        break
            else:
                break
        self.rows = tuple(sorted(data.items()))
        for code in (tuple(data), tuple(data.values())):
            ordered = sorted(code)
            if any(set(w) - {"0", "1"} for w in ordered):
                raise ValueError("Nonbinary prefix")
            if any(v.startswith(u) for u, v in zip(ordered, ordered[1:])):
                raise ValueError("Non-disjoint prefix code")
            if sum((Fraction(1, 2 ** len(w)) for w in code), Fraction()) != 1:
                raise ValueError("Incomplete prefix code")

    def __mul__(self, other):
        if time.monotonic() > Prefix.deadline:
            raise TimeoutError("Ten-second exact replay budget exceeded")
        Prefix.products += 1
        rows = []
        for source, middle in other.rows:
            for domain, target in self.rows:
                if middle.startswith(domain):
                    rows.append((source, target + middle[len(domain):]))
                elif domain.startswith(middle):
                    rows.append((source + domain[len(middle):], target))
        return Prefix(rows)

    def __invert__(self):
        return Prefix((v, u) for u, v in self.rows)

    def __pow__(self, exponent):
        value = Prefix((("", ""),))
        for _ in range(exponent):
            value = value * self
        return value

    def is_identity(self):
        return all(u == v for u, v in self.rows)


CELLS = dict(zip("abcdefg", ("000", "001", "010", "011", "100", "101", "11")))


def cell(word):
    return CELLS[word[0]] + word[1:]


def permutation(*cycles):
    images = {x: x for x in CELLS}
    for cycle in cycles:
        for x, y in zip(cycle, cycle[1:] + cycle[:1]):
            images[x] = y
    return Prefix((CELLS[x], CELLS[y]) for x, y in images.items())


def swap(left, right):
    if left.startswith(right) or right.startswith(left):
        raise ValueError("Swap cylinders must be incomparable")
    todo, code = [""], []
    while todo:
        word = todo.pop()
        if word in (left, right) or not (left.startswith(word) or right.startswith(word)):
            code.append(word)
        else:
            todo.extend((word + "0", word + "1"))
    return Prefix((w, right if w == left else left if w == right else w) for w in code)


def diagonal(value):
    rows = [(CELLS["g"], CELLS["g"])]
    standard = ("00", "01", "1")
    for labels in ("abc", "fed"):
        todo = list(value.rows)
        while todo:
            source, target = todo.pop()
            i = next((i for i, w in enumerate(standard) if source.startswith(w)), None)
            j = next((j for j, w in enumerate(standard) if target.startswith(w)), None)
            if i is None or j is None:
                todo.extend((source + bit, target + bit) for bit in "01")
            else:
                rows.append((CELLS[labels[i]] + source[len(standard[i]):],
                             CELLS[labels[j]] + target[len(standard[j]):]))
    return Prefix(rows)


def comm(x, y):
    return x * y * ~x * ~y


def conj(x, actor):
    return ~actor * x * actor


def thompson_rows(A, B, D):
    common = conj(A, ~B * D * A * D * conj(A, B) * conj(A, ~B * A))
    return {
        "rho_1": A ** 2,
        "rho_2": B ** 3,
        "rho_3": (A * B) ** 4,
        "rho_4": conj(D, A * D) * ~A,
        "rho_5": ~D * conj(A, B * D * A * D * A * conj(A, B * A))
                     * conj(A, ~B * D * A * D * A * conj(A, ~B * A)),
        "rho_6": comm(conj(A, ~B * D * A * D), common),
        "rho_7": comm(conj(A, B * D * A * D), common),
        "rho_8": comm(conj(A, B * D * conj(A, B * D * A)),
                      conj(A, B * D * A * D * conj(A, B) * conj(A, ~B * A))),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        parser.error("Output already exists")
    started = time.monotonic()
    Prefix.deadline = started + 10.0
    C, Y = permutation("abc", "dfe"), permutation("bd", "fg")
    d = comm(Y, C * Y * ~C)
    h = ~C * d * C
    a, e = comm(d, h), C * d * ~C
    A = a * e * ~a
    D = ~C * A * C
    p0, q0 = C * Y * ~C, comm(~C * Y * C, a)
    X0 = p0 * q0 * p0
    actual = dict(d=d, h=h, a=a, e=e, A=A, D=D, p0=p0, q0=q0, X0=X0)
    expected = {name: permutation(*cycles) for name, cycles in {
        "d": ("ce", "fg"), "h": ("bf", "dg"), "a": ("bd", "fg"),
        "e": ("ad", "eg"), "A": ("ab", "ef"), "D": ("ac", "df"),
        "p0": ("cf", "eg"), "q0": ("bf", "dg"), "X0": ("bc", "de"),
    }.items()}
    checks = {"constant_" + k: (v * ~expected[k]).is_identity() for k, v in actual.items()}
    Av, Bv, Dv = swap("00", "01"), swap("01", "10") * swap("01", "11"), swap("1", "00")
    B0 = swap(cell("b"), cell("c0")) * swap(cell("b"), cell("c1"))
    B0 = B0 * swap(cell("e"), cell("d0")) * swap(cell("e"), cell("d1"))
    for name, left, right in (("A", A, Av), ("B", B0, Bv), ("D", D, Dv), ("C", C, Dv * Av)):
        checks["diagonal_" + name] = (left * ~diagonal(right)).is_identity()
    for name, row in {"C_cube": C ** 3, "Y_square": Y ** 2,
                      "d_square": d ** 2, "anchor": (A * C) ** 2,
                      **thompson_rows(A, B0, D)}.items():
        checks[name] = row.is_identity()
    failed = [name for name, passed in checks.items() if not passed]
    if failed:
        raise AssertionError("Exact replay failed: " + ", ".join(failed))
    report = {
        "status": "ok",
        "scope": "Exact constants and diagonal Thompson rows only; no completing Z or hyperlinear model.",
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "all_checks_passed": all(checks.values()), "checks": checks,
        "tables": {k: list(v.rows) for k, v in {"C": C, "Y": Y, "A": A, "B0": B0, "D": D}.items()},
        "prefix_products": Prefix.products, "maximum_table_rows": Prefix.max_rows,
        "prefix_table_row_cap": Prefix.row_cap,
        "seconds": time.monotonic() - started,
    }
    if report["seconds"] > 10:
        raise TimeoutError("Ten-second exact replay budget exceeded")
    with args.output.open("x") as stream:
        json.dump(report, stream, indent=2)
        stream.write("\n")
    print(json.dumps({k: report[k] for k in
                     ("status", "checks", "prefix_products", "maximum_table_rows", "seconds")},
                     separators=(",", ":")))


if __name__ == "__main__":
    main()
