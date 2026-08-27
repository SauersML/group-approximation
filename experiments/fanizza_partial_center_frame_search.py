#!/usr/bin/env python3
"""Search rank-three source-fixed Fanizza frames using arbitrary dual words.

After atom normalization, the baseline commutation matrix is the identity.
Instead of retaining a coordinate pivot, choose baseline p- and q-words
``u`` and ``v`` with ``u dot v = 1``.  Together with the named relative
Schur pair they give the symbolic 2-by-2 block

    [[u^T M v, u^T M e_*], [e_*^T M v, e_*^T M e_*]].

The desired partial-center chart has affine span rank three, invariant
plus/minus coefficient kernels, a stationary cancellation at the bad atom,
and a rank-two plus character represented by a minus character with the same
source atom.  Candidates are enumerated by increasing total word weight.
"""
from __future__ import annotations

import argparse
from itertools import combinations, permutations, product

from fanizza_atom_paired_frame_search import (
    IDENTITY4,
    PLUS_WORDS,
    Matrix4,
    add_vectors,
    affine_vector,
    alternating_form,
    atom_normal_form,
    combined_columns,
    dot,
    evaluated_frame_matrix,
    evaluated_frame_rank,
    frame_columns,
    kernel_code,
    kernel_vectors,
    predicate_menu,
    rank_f2,
    transform_kernel,
)
from fanizza_fixed_predicate_rank_compiler import Affine, bdd_rank_compiler, best_compiler

BitVector = tuple[int, ...]
SWAP_BOTH: Matrix4 = (
    (0, 1, 0, 0),
    (1, 0, 0, 0),
    (0, 0, 0, 1),
    (0, 0, 1, 0),
)


def frame_compatible_compiler(name, arity, predicate):
    """Spend one baseline pivot on C17 to cover its asymmetric bad atom."""
    if name != "conjunction-graph":
        return best_compiler(arity, predicate)[2]
    cube = tuple(product((0, 1), repeat=arity))
    table = {atom: int(predicate(atom)) for atom in cube}
    matrix, baseline = bdd_rank_compiler(table, (0, 1, 2))
    assert baseline == 6
    return matrix


def bounded_words(size: int, maximum_weight: int) -> tuple[BitVector, ...]:
    words = []
    for weight in range(1, min(size, maximum_weight) + 1):
        for support in combinations(range(size), weight):
            word = [0] * size
            for index in support:
                word[index] = 1
            words.append(tuple(word))
    return tuple(words)


def bilinear_affine(
    left: BitVector, matrix: list[list[Affine]], right: BitVector
) -> Affine:
    width = len(matrix[0][0][1]) + 1
    value = (0,) * width
    for row, left_bit in enumerate(left):
        if not left_bit:
            continue
        for column, right_bit in enumerate(right):
            if right_bit:
                value = add_vectors(value, affine_vector(matrix[row][column]))
    return value[0], value[1:]


def dual_block(
    matrix: list[list[Affine]], left: BitVector, right: BitVector
) -> list[list[Affine]]:
    last = len(matrix) - 1
    relative = tuple(int(index == last) for index in range(len(matrix)))
    left_full = left + (0,)
    right_full = right + (0,)
    return [
        [
            bilinear_affine(left_full, matrix, right_full),
            bilinear_affine(left_full, matrix, relative),
        ],
        [
            bilinear_affine(relative, matrix, right_full),
            bilinear_affine(relative, matrix, relative),
        ],
    ]


def affine_span_rank(block: list[list[Affine]]) -> int:
    return rank_f2([list(affine_vector(entry)) for row in block for entry in row])


def find_witness(
    matrix: list[list[Affine]],
    atom: tuple[int, ...],
    maximum_weight: int,
    allowed_kernels: set[int] | None = None,
):
    transformed = atom_normal_form(matrix, atom)
    baseline = len(matrix) - 1
    words = bounded_words(baseline, maximum_weight)
    characters = tuple(product((0, 1), repeat=len(atom) + 1))
    source_character = (1,) + atom
    tested = 0
    rank_three = 0

    for total_weight in range(2, 2 * maximum_weight + 1):
        for left in words:
            left_weight = sum(left)
            if left_weight >= total_weight:
                continue
            for right in words:
                if left_weight + sum(right) != total_weight or dot(left, right) != 1:
                    continue
                tested += 1
                block = dual_block(transformed, left, right)
                if affine_span_rank(block) != 3:
                    continue
                rank_three += 1
                symbolic = alternating_form(block)
                minus_kernel = kernel_code(frame_columns(symbolic, IDENTITY4))
                if allowed_kernels is not None and minus_kernel not in allowed_kernels:
                    continue
                if minus_kernel != kernel_code(frame_columns(symbolic, PLUS_WORDS)):
                    continue
                if kernel_code(combined_columns(symbolic, IDENTITY4)) != kernel_code(
                    combined_columns(symbolic, PLUS_WORDS)
                ):
                    continue
                assert evaluated_frame_rank(
                    symbolic, source_character, source_character, IDENTITY4
                ) == 0
                for coefficient_character in characters:
                    # The reverse reservoir must be uniform across atoms.  We
                    # insist that both sides of the rank-two escape lie in the
                    # J=+1 coefficient sector (character bit zero).
                    if coefficient_character[0] != 0:
                        continue
                    plus_matrix = evaluated_frame_matrix(
                        symbolic,
                        source_character,
                        coefficient_character,
                        PLUS_WORDS,
                    )
                    if rank_f2(plus_matrix) != 2:
                        continue
                    for target_character in characters:
                        if target_character[0] != 0:
                            continue
                        if evaluated_frame_matrix(
                            symbolic,
                            source_character,
                            target_character,
                            IDENTITY4,
                        ) == plus_matrix:
                            return {
                                "left": left,
                                "right": right,
                                "coefficient": coefficient_character,
                                "target": target_character,
                                "tested": tested,
                                "rank_three": rank_three,
                                "kernel": minus_kernel,
                                "hard_form": tuple(
                                    plus_matrix[left][right]
                                    for left, right in (
                                        (0, 1),
                                        (0, 2),
                                        (0, 3),
                                        (1, 2),
                                        (1, 3),
                                        (2, 3),
                                    )
                                ),
                            }
    return {"tested": tested, "rank_three": rank_three}


def audit(
    maximum_weight: int,
    representatives_only: bool,
    predicate_filter: str | None,
    require_support_orbit: bool,
) -> set[int]:
    solved = 0
    total = 0
    witness_kernels: set[int] = set()
    hard_forms: set[tuple[int, ...]] = set()
    allowed_kernels = support_orbit_kernels() if require_support_orbit else None
    for name, arity, predicate in predicate_menu():
        if predicate_filter is not None and name != predicate_filter:
            continue
        matrix = frame_compatible_compiler(name, arity, predicate)
        atoms = [atom for atom in product((0, 1), repeat=arity) if predicate(atom)]
        if representatives_only:
            atoms = atoms[:1]
        for atom in atoms:
            total += 1
            result = find_witness(matrix, atom, maximum_weight, allowed_kernels)
            if "left" in result:
                solved += 1
                witness_kernels.add(result["kernel"])
                hard_forms.add(result["hard_form"])
                print(f"{name} atom={atom}: WITNESS {result}")
                assert result["coefficient"][0] == result["target"][0] == 0
            else:
                print(f"{name} atom={atom}: none {result}")
    print(
        f"rank-three partial-center witnesses={solved}/{total}; "
        f"maximum baseline word weight={maximum_weight}"
    )
    print(f"distinct witness kernels={len(witness_kernels)} codes={witness_kernels}")
    print(f"distinct rank-two escape forms={len(hard_forms)} forms={hard_forms}")
    if predicate_filter is None and not representatives_only:
        assert solved == total == 26
        assert witness_kernels == {symmetric_kernel_code()}
        assert hard_forms == {
            (0, 1, 0, 0, 0, 0),
            (0, 0, 0, 0, 1, 0),
        }
        symmetric_vectors = kernel_vectors(symmetric_kernel_code())
        assert transform_kernel(SWAP_BOTH, symmetric_vectors) == symmetric_vectors
    return witness_kernels


def support_kernel() -> int:
    support_block: list[list[Affine]] = [
        [(1, (0, 0)), (1, (1, 0))],
        [(0, (0, 1)), (0, (0, 0))],
    ]
    return kernel_code(frame_columns(alternating_form(support_block), IDENTITY4))


def vectors_code(vectors: set[tuple[int, ...]]) -> int:
    index = {vector: position for position, vector in enumerate(product((0, 1), repeat=6))}
    return sum(1 << index[vector] for vector in vectors)


def symmetric_kernel_code() -> int:
    zero = (0,) * 6
    generators = (
        (1, 0, 0, 0, 0, 0),
        (0, 0, 0, 0, 0, 1),
        (0, 0, 1, 1, 0, 0),
    )
    vectors = {
        add_vectors(zero, *(generator for bit, generator in zip(bits, generators) if bit))
        for bits in product((0, 1), repeat=3)
    }
    return vectors_code(vectors)


def support_orbit_kernels() -> set[int]:
    source_vectors = kernel_vectors(support_kernel())
    orbit = set()
    for flat in product((0, 1), repeat=16):
        change: Matrix4 = tuple(
            tuple(flat[4 * row : 4 * row + 4]) for row in range(4)
        )  # type: ignore[assignment]
        if rank_f2([list(row) for row in change]) == 4:
            orbit.add(vectors_code(transform_kernel(change, source_vectors)))
    return orbit


def compare_support_orbit(target_kernel: int) -> None:
    source_vectors = kernel_vectors(support_kernel())
    target_vectors = kernel_vectors(target_kernel)
    changes = []
    for flat in product((0, 1), repeat=16):
        change: Matrix4 = tuple(
            tuple(flat[4 * row : 4 * row + 4]) for row in range(4)
        )  # type: ignore[assignment]
        if rank_f2([list(row) for row in change]) != 4:
            continue
        if transform_kernel(change, source_vectors) == target_vectors:
            changes.append(change)
            break
    print(
        f"support kernel={support_kernel()} target kernel={target_kernel} "
        f"same_GL4_orbit={bool(changes)} first_change={changes[:1]}"
    )


def audit_compiler_orders(maximum_weight: int, predicate_filter: str | None) -> None:
    """Test whether a single OBDD order covers every bad atom of a predicate."""
    for name, arity, predicate in predicate_menu():
        if predicate_filter is not None and name != predicate_filter:
            continue
        cube = tuple(product((0, 1), repeat=arity))
        table = {atom: int(predicate(atom)) for atom in cube}
        bad_atoms = tuple(atom for atom in cube if predicate(atom))
        for order in permutations(range(arity)):
            matrix, baseline = bdd_rank_compiler(table, order)
            solved = []
            for atom in bad_atoms:
                result = find_witness(matrix, atom, maximum_weight)
                if "left" in result:
                    solved.append(atom)
            print(
                f"{name} order={order} baseline={baseline}: "
                f"solved={len(solved)}/{len(bad_atoms)} missing="
                f"{[atom for atom in bad_atoms if atom not in solved]}"
            )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-weight", type=int, default=3)
    parser.add_argument("--representatives-only", action="store_true")
    parser.add_argument("--predicate")
    parser.add_argument("--all-orders", action="store_true")
    parser.add_argument("--compare-support", action="store_true")
    parser.add_argument("--require-support-orbit", action="store_true")
    arguments = parser.parse_args()
    if arguments.all_orders:
        audit_compiler_orders(arguments.max_weight, arguments.predicate)
    else:
        kernels = audit(
            arguments.max_weight,
            arguments.representatives_only,
            arguments.predicate,
            arguments.require_support_orbit,
        )
        if arguments.compare_support:
            assert len(kernels) == 1
            compare_support_orbit(next(iter(kernels)))
