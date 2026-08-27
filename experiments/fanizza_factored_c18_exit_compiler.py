#!/usr/bin/env python3
"""Factor C18 residual gates through one affine phase-parity bit.

The 20 positive residual occurrences are h*p*(1-r), h*q*(1-r), and
h*p*q*r.  Compile the first two as three-bit predicates and the last as a
four-bit predicate, then substitute h=1+x_3+x_4+x_5 into every affine matrix
entry.  Verify all original six-bit atoms and search the symmetric frames.
"""
from __future__ import annotations

from itertools import product

from fanizza_fixed_predicate_rank_compiler import Affine, best_compiler
from fanizza_partial_center_frame_search import find_witness, symmetric_kernel_code
from fanizza_oriented_c18_exit_compiler import even_phase, first_exit, second_exit


def substitute(matrix: list[list[Affine]], source_indices: tuple[int, ...]) -> list[list[Affine]]:
    """Substitute compressed variables followed by h into six original bits."""
    out: list[list[Affine]] = []
    for row in matrix:
        out_row = []
        for constant, coefficients in row:
            expanded = [0] * 6
            for coefficient, index in zip(coefficients[:-1], source_indices):
                expanded[index] ^= coefficient
            phase = coefficients[-1]
            constant ^= phase
            for index in (3, 4, 5):
                expanded[index] ^= phase
            out_row.append((constant, tuple(expanded)))
        out.append(out_row)
    return out


def p_gate(assignment: tuple[int, ...]) -> bool:
    p, _, target, j, xzx, z = assignment
    return bool(p) and not target and even_phase((j, xzx, z))


def q_gate(assignment: tuple[int, ...]) -> bool:
    _, q, target, j, xzx, z = assignment
    return bool(q) and not target and even_phase((j, xzx, z))


def overlap_gate(assignment: tuple[int, ...]) -> bool:
    p, q, target, j, xzx, z = assignment
    return bool(p and q and target) and even_phase((j, xzx, z))


def compiler(predicate, arity: int, source_indices: tuple[int, ...]):
    baseline, order, matrix = best_compiler(arity, predicate)
    return baseline, order, substitute(matrix, source_indices)


def audit(maximum_weight: int = 2) -> None:
    cube = tuple(product((0, 1), repeat=6))
    for assignment in cube:
        factored = sum(int(predicate(assignment)) for predicate in (p_gate, q_gate, overlap_gate))
        oriented = int(first_exit(assignment)) + int(second_exit(assignment))
        assert factored == oriented

    menus = (
        (
            "p(1-r)h",
            p_gate,
            compiler(lambda x: x[0] and not x[1] and x[2], 3, (0, 2)),
        ),
        (
            "q(1-r)h",
            q_gate,
            compiler(lambda x: x[0] and not x[1] and x[2], 3, (1, 2)),
        ),
        (
            "pqrh",
            overlap_gate,
            compiler(lambda x: x[0] and x[1] and x[2] and x[3], 4, (0, 1, 2)),
        ),
    )

    solved = 0
    total = 0
    kernels = set()
    forms = set()
    frame_words: dict[str, set[tuple[tuple[int, ...], tuple[int, ...]]]] = {}
    for name, predicate, (baseline, order, matrix) in menus:
        frame_words[name] = set()
        atoms = [assignment for assignment in cube if predicate(assignment)]
        print(
            f"{name}: atoms={len(atoms)} compressed_order={order} "
            f"baseline={baseline} matrix={len(matrix)}"
        )
        for atom in atoms:
            total += 1
            witness = find_witness(matrix, atom, maximum_weight)
            if "left" not in witness:
                print(f"  atom={atom}: NO FRAME {witness}")
                continue
            solved += 1
            kernels.add(witness["kernel"])
            forms.add(witness["hard_form"])
            frame_words[name].add((witness["left"], witness["right"]))
            print(
                f"  atom={atom}: left={witness['left']} right={witness['right']} "
                f"hard={witness['hard_form']}"
            )

    print(f"factored frames={solved}/{total} kernels={kernels} hard_forms={forms}")
    assert solved == total == 20
    assert kernels == {symmetric_kernel_code()}
    assert forms == {(0, 1, 0, 0, 0, 0)}
    assert all(len(words) == 1 for words in frame_words.values())
    print(f"per-gate frame words={frame_words}")


if __name__ == "__main__":
    audit()
