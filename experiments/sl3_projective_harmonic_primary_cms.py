"""Solve exported harmonic bit-vector systems with CryptoMiniSat.

This is a standalone companion to
``sl3_projective_harmonic_primary_smt.py``: it does not need Sage.  It reads
the sparse ``QF_BV`` equations emitted by that exporter, compiles each
three-bit modular sum to native XOR clauses and ripple-carry gates, and writes
a Z3-style value list.  The value list is subsequently checked against the
original Sage integer boundary by the exporter in ``--model`` mode.
"""

from __future__ import annotations

import argparse
import json
import re
import time
from pathlib import Path

from pycryptosat import Solver


DECLARATION = re.compile(
    r"^\(declare-fun x(\d+) \(\) \(_ BitVec (\d+)\)\)$")


def parse_expression(tokens: list[str], position: int = 0):
    token = tokens[position]
    if token != "(":
        return token, position + 1
    result = []
    position += 1
    while tokens[position] != ")":
        child, position = parse_expression(tokens, position)
        result.append(child)
    return result, position + 1


def tokenize(line: str) -> list[str]:
    return line.replace("(", " ( ").replace(")", " ) ").split()


def linear_terms(expression, modulus: int) -> list[tuple[int, int]]:
    if isinstance(expression, str):
        if not expression.startswith("x"):
            raise ValueError(f"unexpected linear atom {expression}")
        return [(int(expression[1:]), 1)]
    operator = expression[0]
    if operator == "bvadd":
        return linear_terms(expression[1], modulus) + linear_terms(
            expression[2], modulus)
    if operator == "bvneg":
        return [
            (index, -coefficient % modulus)
            for index, coefficient in linear_terms(expression[1], modulus)
        ]
    if operator == "bvmul":
        coefficient = int(expression[1][2:], 2)
        return [
            (index, coefficient * value % modulus)
            for index, value in linear_terms(expression[2], modulus)
        ]
    raise ValueError(f"unexpected bit-vector operator {operator}")


def parse_instance(path: Path):
    variable_count = 0
    width = None
    equations = []
    with path.open(encoding="utf-8") as stream:
        for raw_line in stream:
            line = raw_line.strip()
            declaration = DECLARATION.match(line)
            if declaration:
                index, declared_width = map(int, declaration.groups())
                if index != variable_count:
                    raise ValueError("bit-vector variables are not consecutive")
                variable_count += 1
                if width is None:
                    width = declared_width
                elif width != declared_width:
                    raise ValueError("mixed bit-vector widths")
                continue
            if not line.startswith("(assert"):
                continue
            syntax, end = parse_expression(tokenize(line))
            if end != len(tokenize(line)) or syntax[0] != "assert":
                raise ValueError("invalid assertion syntax")
            equality = syntax[1]
            if equality[0] != "=":
                raise ValueError("assertion is not an equality")
            if width is None:
                raise ValueError("assertion precedes declarations")
            modulus = 1 << width
            right_side = int(equality[2][2:], 2)
            equations.append((linear_terms(equality[1], modulus), right_side))
    if width is None:
        raise ValueError("instance has no bit-vector variables")
    return variable_count, width, equations


class Circuit:
    def __init__(self, solver: Solver):
        self.solver = solver
        self.variable_count = 0
        self.clause_count = 0
        self.xor_count = 0
        self.false = self.new_variable()
        self.add_clause([-self.false])

    def new_variable(self) -> int:
        self.variable_count += 1
        return self.variable_count

    def new_bits(self, width: int) -> tuple[int, ...]:
        return tuple(self.new_variable() for _ in range(width))

    def add_clause(self, clause: list[int]) -> None:
        self.solver.add_clause(clause)
        self.clause_count += 1

    def add_xor(self, variables: list[int], parity: bool) -> None:
        odd = set()
        for variable in variables:
            if variable in odd:
                odd.remove(variable)
            else:
                odd.add(variable)
        if not odd:
            if parity:
                self.add_clause([])
            return
        self.solver.add_xor_clause(sorted(odd), parity)
        self.xor_count += 1

    def add_and(self, left: int, right: int, output: int) -> None:
        self.add_clause([-left, -right, output])
        self.add_clause([left, -output])
        self.add_clause([right, -output])

    def add_majority(
            self, first: int, second: int, third: int, output: int) -> None:
        self.add_clause([-first, -second, output])
        self.add_clause([-first, -third, output])
        self.add_clause([-second, -third, output])
        self.add_clause([first, second, -output])
        self.add_clause([first, third, -output])
        self.add_clause([second, third, -output])

    def add_words(
            self, left: tuple[int, ...], right: tuple[int, ...]
    ) -> tuple[int, ...]:
        width = len(left)
        result = self.new_bits(width)
        self.add_xor([result[0], left[0], right[0]], False)
        if width == 1:
            return result
        carry = self.new_variable()
        self.add_and(left[0], right[0], carry)
        for bit in range(1, width):
            self.add_xor(
                [result[bit], left[bit], right[bit], carry], False)
            if bit + 1 < width:
                next_carry = self.new_variable()
                self.add_majority(
                    left[bit], right[bit], carry, next_carry)
                carry = next_carry
        return result

    def scale_word(
            self, word: tuple[int, ...], coefficient: int
    ) -> tuple[int, ...]:
        width = len(word)
        modulus = 1 << width
        coefficient %= modulus
        if coefficient == 1:
            return word
        output = self.new_bits(width)
        for source_value in range(modulus):
            target_value = coefficient * source_value % modulus
            antecedent_negation = [
                -word[bit] if source_value & (1 << bit) else word[bit]
                for bit in range(width)
            ]
            for bit in range(width):
                target_literal = (
                    output[bit]
                    if target_value & (1 << bit) else -output[bit]
                )
                self.add_clause(antecedent_negation + [target_literal])
        return output

    def constrain_word(self, word: tuple[int, ...], value: int) -> None:
        for bit, variable in enumerate(word):
            self.add_clause([
                variable if value & (1 << bit) else -variable
            ])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("instance", type=Path)
    parser.add_argument("model_output", type=Path)
    parser.add_argument("--time-limit", type=float, default=600.0)
    parser.add_argument("--threads", type=int, default=1)
    args = parser.parse_args()
    if args.threads < 1:
        raise ValueError("thread count must be positive")

    source_variable_count, width, equations = parse_instance(args.instance)
    solver = Solver(
        verbose=0, time_limit=args.time_limit, threads=args.threads)
    circuit = Circuit(solver)
    words = [circuit.new_bits(width) for _ in range(source_variable_count)]
    modulus = 1 << width
    for terms, right_side in equations:
        operands = [
            circuit.scale_word(words[index], coefficient)
            for index, coefficient in terms
        ]
        if not operands:
            if right_side % modulus:
                circuit.add_clause([])
            continue
        accumulator = operands[0]
        for operand in operands[1:]:
            accumulator = circuit.add_words(accumulator, operand)
        circuit.constrain_word(accumulator, right_side)

    started = time.monotonic()
    status, model = solver.solve()
    elapsed = time.monotonic() - started
    if status is True:
        with args.model_output.open("w", encoding="utf-8") as output:
            output.write("sat\n(")
            for index, word in enumerate(words):
                value = sum(
                    1 << bit for bit, variable in enumerate(word)
                    if model[variable]
                )
                output.write(f"(x{index} #b{value:0{width}b})")
            output.write(")\n")
    else:
        args.model_output.write_text(
            "unsat\n" if status is False else "unknown\n", encoding="utf-8")
    print(json.dumps({
        "bit_width": width,
        "source_variable_count": source_variable_count,
        "solver_threads": args.threads,
        "equation_count": len(equations),
        "boolean_variable_count": circuit.variable_count,
        "cnf_clause_count": circuit.clause_count,
        "xor_clause_count": circuit.xor_count,
        "solver_status": status,
        "elapsed_seconds": elapsed,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
