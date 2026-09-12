#!/usr/bin/env python3
"""Verify the gatewise Cook--Levin rank energy over F_2.

Every gate contributes a two-by-two affine matrix whose F_2 rank is one
plus its Boolean consistency-violation bit.  Direct sums therefore have
rank equal to the number of gates plus the number of violated gates.
"""

from itertools import product


def rank_f2(matrix: list[list[int]]) -> int:
    work = [row[:] for row in matrix]
    rank = 0
    for column in range(len(work[0]) if work else 0):
        pivot = next(
            (row for row in range(rank, len(work)) if work[row][column]),
            None,
        )
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        for row in range(len(work)):
            if row != rank and work[row][column]:
                work[row] = [a ^ b for a, b in zip(work[row], work[rank])]
        rank += 1
    return rank


def gate_block(kind: str, inputs: tuple[int, ...], output: int) -> tuple[list[list[int]], int]:
    if kind == "and":
        x, y = inputs
        violation = output ^ (x & y)
        return [[1, x], [y, output]], violation
    if kind == "copy":
        (x,) = inputs
        violation = x ^ output
    elif kind == "not":
        (x,) = inputs
        violation = 1 ^ x ^ output
    elif kind == "xor":
        x, y = inputs
        violation = x ^ y ^ output
    else:
        raise ValueError(f"unknown gate kind: {kind}")
    return [[1, 0], [0, violation]], violation


def block_sum(blocks: list[list[list[int]]]) -> list[list[int]]:
    size = sum(len(block) for block in blocks)
    result = [[0] * size for _ in range(size)]
    offset = 0
    for block in blocks:
        for row in range(len(block)):
            for column in range(len(block[row])):
                result[offset + row][offset + column] = block[row][column]
        offset += len(block)
    return result


def verify_gate_tables() -> None:
    for kind, arity in (("and", 2), ("copy", 1), ("not", 1), ("xor", 2)):
        for values in product((0, 1), repeat=arity + 1):
            block, violation = gate_block(kind, values[:-1], values[-1])
            assert rank_f2(block) == 1 + violation


def verify_sample_circuit() -> None:
    # Complete wire assignments are deliberately unrestricted: internal wires
    # may be inconsistent, and each inconsistent gate must contribute one.
    gates = (
        ("and", (0, 1), 2),
        ("not", (2,), 3),
        ("xor", (3, 0), 4),
        ("copy", (4,), 5),
    )
    for wires in product((0, 1), repeat=6):
        blocks = []
        unsat = 0
        for kind, input_wires, output_wire in gates:
            block, violation = gate_block(
                kind,
                tuple(wires[index] for index in input_wires),
                wires[output_wire],
            )
            blocks.append(block)
            unsat += violation
        assert rank_f2(block_sum(blocks)) == len(gates) + unsat


if __name__ == "__main__":
    verify_gate_tables()
    verify_sample_circuit()
    print("verified four gate tables and all 64 complete assignments of the sample circuit")
