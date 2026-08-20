#!/usr/bin/env python3
"""Optimize and verify rank gates for Fanizza et al.'s fixed nonlinear menu.

The generic Schur--Clifford compiler uses one internally disjoint path for
every satisfying assignment.  Here the relevant predicates are fixed and
small, so a reduced ordered binary decision diagram gives a much smaller
algebraic branching program.  Every input follows exactly one live path;
the path sum is therefore the predicate over F_2.

This file is deliberately standalone so that the finite audit can be run on
an MSI compute node without importing the rest of the repository.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import permutations, product
from typing import Callable, Iterable

BitTuple = tuple[int, ...]
Affine = tuple[int, BitTuple]


def zero(k: int) -> Affine:
    return (0, (0,) * k)


def one(k: int) -> Affine:
    return (1, (0,) * k)


def literal(k: int, variable: int, bit: int) -> Affine:
    coefficients = [0] * k
    coefficients[variable] = 1
    return (0 if bit else 1, tuple(coefficients))


def affine_add(left: Affine, right: Affine) -> Affine:
    return (
        left[0] ^ right[0],
        tuple(a ^ b for a, b in zip(left[1], right[1])),
    )


def evaluate_affine(form: Affine, assignment: BitTuple) -> int:
    value = form[0]
    for coefficient, bit in zip(form[1], assignment):
        value ^= coefficient & bit
    return value


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


@dataclass(frozen=True)
class Node:
    variable: int
    low: int
    high: int


def ordered_bdd(
    table: dict[BitTuple, int], order: tuple[int, ...]
) -> tuple[int, tuple[Node, ...], int, int]:
    """Return root, nodes, false terminal, true terminal for a reduced OBDD."""
    k = len(order)
    false_terminal = 0
    true_terminal = 1
    nodes: list[Node] = []
    unique: dict[Node, int] = {}

    def descend(level: int, partial: dict[int, int]) -> int:
        if level == k:
            assignment = tuple(partial[index] for index in range(k))
            return true_terminal if table[assignment] else false_terminal
        variable = order[level]
        partial[variable] = 0
        low = descend(level + 1, partial)
        partial[variable] = 1
        high = descend(level + 1, partial)
        del partial[variable]
        if low == high:
            return low
        candidate = Node(variable, low, high)
        if candidate not in unique:
            unique[candidate] = len(nodes) + 2
            nodes.append(candidate)
        return unique[candidate]

    root = descend(0, {})
    return root, tuple(nodes), false_terminal, true_terminal


def bdd_rank_compiler(
    table: dict[BitTuple, int], order: tuple[int, ...]
) -> tuple[list[list[Affine]], int]:
    """Build the Schur matrix from the reduced OBDD path-sum."""
    k = len(order)
    root, nodes, false_terminal, true_terminal = ordered_bdd(table, order)
    by_id = {index + 2: node for index, node in enumerate(nodes)}

    if root == false_terminal:
        # A disconnected source and sink have zero path-sum.
        vertex_ids = (-1, true_terminal)
        source_id = -1
        edges: list[tuple[int, int, Affine]] = []
    elif root == true_terminal:
        vertex_ids = (true_terminal,)
        source_id = true_terminal
        edges = []
    else:
        reachable: set[int] = set()
        frontier = [root]
        while frontier:
            identifier = frontier.pop()
            if identifier in reachable or identifier in (false_terminal, true_terminal):
                continue
            reachable.add(identifier)
            node = by_id[identifier]
            frontier.extend((node.low, node.high))
        # Every edge raises the variable's position in the chosen order.  Sorting
        # by that position therefore gives a topological order.
        position = {variable: index for index, variable in enumerate(order)}
        vertex_ids = tuple(
            sorted(reachable, key=lambda identifier: position[by_id[identifier].variable])
        ) + (true_terminal,)
        source_id = root
        edges = []
        for identifier in vertex_ids[:-1]:
            node = by_id[identifier]
            for bit, target in ((0, node.low), (1, node.high)):
                if target != false_terminal:
                    edges.append((identifier, target, literal(k, node.variable, bit)))

    relabel = {identifier: index for index, identifier in enumerate(vertex_ids)}
    size = len(vertex_ids)
    adjacency = [[zero(k) for _ in range(size)] for _ in range(size)]
    for source, target, label in edges:
        row, column = relabel[source], relabel[target]
        adjacency[row][column] = affine_add(adjacency[row][column], label)

    unitriangular = [row[:] for row in adjacency]
    for index in range(size):
        unitriangular[index][index] = affine_add(unitriangular[index][index], one(k))

    schur = [[zero(k) for _ in range(size + 1)] for _ in range(size + 1)]
    for row in range(size):
        for column in range(size):
            schur[row][column] = unitriangular[row][column]
    schur[relabel[true_terminal]][size] = one(k)
    schur[size][relabel[source_id]] = one(k)
    return schur, size


def evaluate_matrix(matrix: list[list[Affine]], assignment: BitTuple) -> list[list[int]]:
    return [
        [evaluate_affine(entry, assignment) for entry in row]
        for row in matrix
    ]


def best_compiler(
    arity: int, predicate: Callable[[BitTuple], bool]
) -> tuple[int, tuple[int, ...], list[list[Affine]]]:
    cube = tuple(product((0, 1), repeat=arity))
    table = {assignment: int(predicate(assignment)) for assignment in cube}
    best: tuple[int, tuple[int, ...], list[list[Affine]]] | None = None
    for order in permutations(range(arity)):
        matrix, baseline = bdd_rank_compiler(table, order)
        for assignment in cube:
            assert rank_f2(evaluate_matrix(matrix, assignment)) == baseline + table[assignment]
        candidate = (baseline, order, matrix)
        if best is None or candidate[:2] < best[:2]:
            best = candidate
    assert best is not None
    return best


def indicator(points: Iterable[BitTuple]) -> Callable[[BitTuple], bool]:
    point_set = frozenset(points)
    return lambda assignment: assignment in point_set


def audit() -> None:
    # C13/C14: (a AND q) differs from (b AND q).
    conjunction_equality_failure = lambda x: bool(x[1] and (x[0] ^ x[2]))

    # C17: d = p AND q.
    conjunction_graph_failure = lambda x: bool(x[0] ^ (x[1] & x[2]))

    # C18 uses -1 -> 1.  Its unsatisfying set is A123 x A456.
    a123 = {(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 1, 1)}
    a456 = {(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)}
    conditional_partition_failure = lambda x: x[:3] in a123 and x[3:] in a456

    predicates = (
        ("conjunction-equality", 3, conjunction_equality_failure),
        ("conjunction-graph", 3, conjunction_graph_failure),
        ("conditional-three-projection-partition", 6, conditional_partition_failure),
    )
    for name, arity, predicate in predicates:
        baseline, order, matrix = best_compiler(arity, predicate)
        satisfying_count = sum(
            predicate(assignment) for assignment in product((0, 1), repeat=arity)
        )
        disjoint_path_baseline = 2 + satisfying_count * (arity - 1)
        print(
            f"{name}: forbidden={satisfying_count}, order={order}, "
            f"baseline={baseline}, matrix={len(matrix)}, "
            f"disjoint-path-baseline={disjoint_path_baseline}"
        )

    # A single forbidden atom is the only additional primitive needed if a
    # later presentation elects to compile atoms separately.
    for arity in range(1, 7):
        point = (1,) * arity
        baseline, order, matrix = best_compiler(arity, indicator((point,)))
        assert baseline == arity + 1
        print(f"atom-{arity}: order={order}, baseline={baseline}, matrix={len(matrix)}")


if __name__ == "__main__":
    audit()
