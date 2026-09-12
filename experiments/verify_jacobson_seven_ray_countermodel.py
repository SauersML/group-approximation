#!/usr/bin/env python3
"""Exact F_2 case checks for the seven-ray quotient and literal TS word.

No finite truncation is used. For each expanded word of length L we check
all basis vectors at levels 0,...,L and one formal level N with N>=L+1.
The only level-changing primitive is H, and it changes a level by at most
one. Consequently every intermediate formal level N+k stays positive.
The symbolic calculation therefore covers every remaining level at once.

This is stdlib exact-arithmetic evidence, not a Lean proof, an MF
construction by itself, or a proof of non-MF existence. Run on MSI only.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import itertools
import json
import os
from pathlib import Path
import resource
import time
from typing import Callable


Matrix = tuple[int, int, int]
IDENTITY: Matrix = (1, 2, 4)
NATURAL_LABELS = (1, 2, 4)
RAY_NAMES = {1: "A1", 2: "A2", 4: "A3", 6: "B1", 5: "B2", 3: "B3", 7: "C"}


def matrix_vector(matrix: Matrix, vector: int) -> int:
    result = 0
    for column in range(3):
        if vector & (1 << column):
            result ^= matrix[column]
    return result


def multiply(left: Matrix, right: Matrix) -> Matrix:
    return tuple(matrix_vector(left, column) for column in right)


def matrix_inverse(matrix: Matrix) -> Matrix:
    return tuple(next(v for v in range(1, 8) if matrix_vector(matrix, v) == e)
                 for e in NATURAL_LABELS)


def root(row: int, column: int) -> Matrix:
    result = list(IDENTITY)
    result[column - 1] ^= 1 << (row - 1)
    return tuple(result)


def swap(first: int, second: int) -> Matrix:
    result = list(IDENTITY)
    result[first - 1], result[second - 1] = result[second - 1], result[first - 1]
    return tuple(result)


@dataclass(frozen=True)
class Level:
    symbolic: bool
    value: int

    def is_positive(self, lower_bound: int) -> bool:
        if self.symbolic:
            if lower_bound + self.value < 1:
                raise AssertionError("Symbolic branch reached the boundary")
            return True
        if self.value < 0:
            raise AssertionError("A negative concrete level was produced")
        return self.value > 0

    def shifted(self, offset: int) -> Level:
        level = Level(self.symbolic, self.value + offset)
        if not level.symbolic and level.value < 0:
            raise AssertionError("A shift left the half-line")
        return level


Basis = tuple[int, Level]
Vector = frozenset[Basis]


@dataclass(frozen=True)
class Operator:
    name: str
    sector: str
    matrix: Matrix = IDENTITY

    def inverse(self) -> Operator:
        if self.sector == "H":
            return self
        return Operator(self.name + "^-1", self.sector, matrix_inverse(self.matrix))


Word = tuple[Operator, ...]
H = Operator("H", "H")


def inverse(word: Word) -> Word:
    return tuple(op.inverse() for op in reversed(word))


def commutator(left: Word, right: Word) -> Word:
    return left + right + inverse(left) + inverse(right)


def packet(name: str, sector: str, matrix: Matrix) -> Word:
    return (Operator(name, sector, matrix),)


def singleton(basis: Basis) -> Vector:
    return frozenset((basis,))


class RayAction:
    def __init__(self, name: str, seven: bool):
        self.name = name
        self.seven = seven
        self.labels = tuple(range(1, 8)) if seven else NATURAL_LABELS

    def primitive(self, op: Operator, basis: Basis, lower_bound: int) -> Vector:
        label, level = basis
        positive = level.is_positive(lower_bound)
        if op.sector == "H":
            if label == 2:
                return singleton((1, level.shifted(1)))
            if label == 1 and positive:
                return singleton((2, level.shifted(-1)))
            if self.seven and positive and label in (6, 5):
                return singleton((5 if label == 6 else 6, level))
            return singleton(basis)

        head_active = not positive and op.sector in ("head", "both")
        tail_active = positive and op.sector in ("tail", "both")
        if head_active and label in NATURAL_LABELS:
            image = matrix_vector(op.matrix, label)
            return frozenset((e, level) for e in NATURAL_LABELS if image & e)
        if tail_active:
            image = matrix_vector(op.matrix, label)
            if self.seven:
                return singleton((image, level))
            return frozenset((e, level) for e in NATURAL_LABELS if image & e)
        return singleton(basis)

    def evaluate(self, word: Word, basis: Basis, lower_bound: int) -> Vector:
        vector = singleton(basis)
        # Matrix products act on column vectors from right to left.
        for op in reversed(word):
            result: set[Basis] = set()
            for term in vector:
                result.symmetric_difference_update(self.primitive(op, term, lower_bound))
            vector = frozenset(result)
        return vector


def describe(vector: Vector) -> list[str]:
    return sorted(f"{RAY_NAMES[label]}@{'N' if level.symbolic else ''}"
                  f"{level.value:+d}" for label, level in vector)


class Checker:
    def __init__(self):
        self.results: list[dict] = []

    def equality(self, action: RayAction, name: str, left: Word, right: Word = (),
                 formula: Callable[[Basis, int], Vector] | None = None) -> None:
        length = max(len(left), len(right))
        cutoff = length + 1
        finite_cases = 0
        symbolic_cases = 0
        levels = [Level(False, n) for n in range(cutoff)] + [Level(True, 0)]
        for level in levels:
            for label in action.labels:
                basis = (label, level)
                actual = action.evaluate(left, basis, cutoff)
                expected = (formula(basis, cutoff) if formula is not None
                            else action.evaluate(right, basis, cutoff))
                if actual != expected:
                    raise AssertionError(json.dumps({
                        "model": action.name, "identity": name,
                        "input": describe(singleton(basis)),
                        "actual": describe(actual), "expected": describe(expected),
                        "symbolic_lower_bound": cutoff,
                    }, sort_keys=True))
                if level.symbolic:
                    symbolic_cases += 1
                else:
                    finite_cases += 1
        self.results.append({
            "model": action.name,
            "identity": name,
            "expanded_left_length": len(left),
            "expanded_right_length": len(right),
            "concrete_levels": [0, cutoff - 1],
            "generic_level": f"N >= {cutoff}",
            "concrete_basis_cases": finite_cases,
            "symbolic_basis_cases": symbolic_cases,
            "status": "PASS",
        })


def head_mark_formula(basis: Basis, _lower_bound: int) -> Vector:
    if basis == (4, Level(False, 0)):
        return frozenset((basis, (1, Level(False, 0))))
    return singleton(basis)


def seven_ts_formula(basis: Basis, _lower_bound: int) -> Vector:
    if basis == (4, Level(False, 0)):
        return frozenset((basis, (1, Level(False, 1)),
                          (3, Level(False, 1)), (2, Level(False, 0))))
    return singleton(basis)


def literal_t_root(basis: Basis, lower_bound: int) -> Vector:
    label, level = basis
    if label == 4 and level.is_positive(lower_bound):
        return frozenset((basis, (2, level.shifted(-1))))
    return singleton(basis)


def literal_s_root(basis: Basis, _lower_bound: int) -> Vector:
    label, level = basis
    if label == 4:
        return frozenset((basis, (1, level.shifted(1))))
    return singleton(basis)


def finite_packet_check() -> tuple[dict, list[Matrix], list[Matrix]]:
    matrices = [tuple(columns) for columns in itertools.product(range(1, 8), repeat=3)
                if len({matrix_vector(tuple(columns), v) for v in range(8)}) == 8]
    if len(matrices) != 168:
        raise AssertionError("GL_3(F_2) order check failed")
    actions = {m: tuple(matrix_vector(m, x) for x in range(1, 8)) for m in matrices}
    if len(set(actions.values())) != 168:
        raise AssertionError("Seven-point action is not faithful")
    products = 0
    for left in matrices:
        for right in matrices:
            product = multiply(left, right)
            if product not in actions:
                raise AssertionError("Matrix group is not closed")
            if actions[product] != tuple(actions[left][x - 1] for x in actions[right]):
                raise AssertionError("Permutation action is not multiplicative")
            products += 1
    generators = [root(i, j) for i in range(1, 4) for j in range(1, 4) if i != j]
    reached = {IDENTITY}
    pending = [IDENTITY]
    while pending:
        current = pending.pop()
        for generator in generators:
            product = multiply(current, generator)
            if product not in reached:
                reached.add(product)
                pending.append(product)
    if reached != set(matrices):
        raise AssertionError("The six root matrices do not generate the finite packet")
    overlap = [m for m in matrices if m[1] == 2 and not ((m[0] | m[2]) & 2)]
    if len(overlap) != 6:
        raise AssertionError("K should be GL_2(F_2) of order six")
    return ({"group_order": 168, "multiplication_pairs": products,
             "faithful_seven_point_images": len(set(actions.values())),
             "natural_head_matrices": len(set(matrices)),
             "root_generator_closure_order": len(reached), "overlap_order": len(overlap),
             "status": "PASS"}, generators, overlap)


def verify() -> dict:
    packet_result, generators, overlap = finite_packet_check()
    checker = Checker()
    seven = RayAction("seven_ray_amenable_quotient", True)
    literal = RayAction("literal_three_ray_jacobson", False)
    h = (H,)
    b = packet("b", "both", swap(2, 3))
    d_p = packet("d_P", "tail", swap(1, 3))
    c = packet("c", "tail", root(1, 3))
    z_p = packet("z_P", "tail", root(2, 3))
    z = packet("z", "both", root(2, 3))
    k = packet("k", "both", root(3, 1))
    b_q = packet("b_Q", "head", root(1, 2))
    w = packet("w", "head", root(1, 3))
    hch = h + c + h
    hzh = h + z + h
    raw_commutation = commutator(hch, z_p)
    u = commutator(hch, k)
    ts_word = commutator(u, hzh) + z

    for action in (seven, literal):
        checker.equality(action, "H^2=1", h + h)
        for index, matrix in enumerate(overlap):
            overlap_word = packet(f"K_{index}", "head", matrix)
            checker.equality(action, f"[H,K_{index}]=1",
                             commutator(h, overlap_word))
        checker.equality(action, "(H b)^3=1", (h + b) * 3)
        checker.equality(action, "(H d_P)^3=1", (h + d_p) * 3)
        checker.equality(action, "R=[H c H,z_P]=1", raw_commutation)
        checker.equality(action, "w is the nontrivial head transvection", w,
                         formula=head_mark_formula)
        marked_basis = (4, Level(False, 0))
        if action.evaluate(w, marked_basis, 1) == singleton(marked_basis):
            raise AssertionError("The head mark vanished")
        for head_index, head_matrix in enumerate(generators):
            for tail_index, tail_matrix in enumerate(generators):
                head = packet(f"head_{head_index}", "head", head_matrix)
                tail = packet(f"tail_{tail_index}", "tail", tail_matrix)
                checker.equality(action, f"[head_{head_index},tail_{tail_index}]=1",
                                 commutator(head, tail))

    checker.equality(seven, "H c H=z_P", hch, z_p)
    checker.equality(seven, "u=x21_P", u, packet("x21_P", "tail", root(2, 1)))
    checker.equality(seven, "W is the stated finite transvection", ts_word,
                     formula=seven_ts_formula)
    checker.equality(seven, "W^2=1", ts_word + ts_word)
    checker.equality(seven, "[b_Q,W]=w", commutator(b_q, ts_word), w)
    if seven.evaluate(ts_word, (4, Level(False, 0)), 1) == singleton((4, Level(False, 0))):
        raise AssertionError("The TS word must be nonidentity in the seven-ray quotient")
    checker.equality(literal, "H c H=x23(T)", hch, formula=literal_t_root)
    checker.equality(literal, "H z H=x13(S)", hzh, formula=literal_s_root)
    checker.equality(literal, "W=1", ts_word)

    return {
        "format": "jacobson-seven-ray-exact-case-check-v1",
        "status": "PASS",
        "arithmetic": "F_2 via symmetric differences; no floating point",
        "coverage": {
            "domain": "all seven-ray and three-ray basis vectors at every nonnegative level",
            "method": "all levels 0..L and a formal N>=L+1 for each expanded length-L word",
            "tail_argument": "Each primitive changes level by at most one; all formal intermediate levels are positive, so no boundary branch is omitted.",
            "not_a_finite_truncation": True,
        },
        "finite_packet": packet_result,
        "identity_checks": checker.results,
        "identity_count": len(checker.results),
        "concrete_basis_cases": sum(r["concrete_basis_cases"] for r in checker.results),
        "symbolic_basis_cases": sum(r["symbolic_basis_cases"] for r in checker.results),
        "scope": "Exact case-check evidence only; not Lean verification, not a proof of amenable-implies-MF, and not a non-MF existence proof.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    # This bounded verification is deliberately run only on Linux MSI.
    affinity = os.sched_getaffinity(0)
    os.sched_setaffinity(0, {min(affinity)})
    resource.setrlimit(resource.RLIMIT_CPU, (18, 18))
    started = time.monotonic()
    report = verify()
    report["verifier_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report["execution"] = {"location": "MSI", "cpu_limit": 1,
                           "cpu_time_limit_seconds": 18,
                           "elapsed_seconds": round(time.monotonic() - started, 6)}
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": report["status"], "identity_count": report["identity_count"],
                      "concrete_basis_cases": report["concrete_basis_cases"],
                      "symbolic_basis_cases": report["symbolic_basis_cases"],
                      "elapsed_seconds": report["execution"]["elapsed_seconds"]}, sort_keys=True))


if __name__ == "__main__":
    main()
