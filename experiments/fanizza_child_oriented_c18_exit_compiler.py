#!/usr/bin/env python3
"""Compile C18 positive residuals after assigning them to recurrence children.

The two predicates below have the same pointwise occurrence count as the
positive-residual plus double-110 decomposition, but each occurrence is tied
to one of the two source projections p and q.  This is the useful orientation
for controlled active/exit transport of the two recurrence children.
"""
from __future__ import annotations

from itertools import product

from fanizza_fixed_predicate_rank_compiler import best_compiler
from fanizza_partial_center_frame_search import find_witness, symmetric_kernel_code
from fanizza_oriented_c18_exit_compiler import even_phase, first_exit, second_exit


def p_child_exit(assignment: tuple[int, ...]) -> bool:
    p, _, target, j, xzx, z = assignment
    return even_phase((j, xzx, z)) and bool(p) and not target


def q_child_exit(assignment: tuple[int, ...]) -> bool:
    p, q, target, j, xzx, z = assignment
    return even_phase((j, xzx, z)) and bool(q) and (not target or bool(p))


def audit(maximum_weight: int = 2) -> None:
    cube = tuple(product((0, 1), repeat=6))
    for assignment in cube:
        residual_count = int(first_exit(assignment)) + int(second_exit(assignment))
        child_count = int(p_child_exit(assignment)) + int(q_child_exit(assignment))
        assert residual_count == child_count

    kernels = set()
    forms = set()
    solved = 0
    total = 0
    for name, predicate in (("p-child", p_child_exit), ("q-child", q_child_exit)):
        baseline, order, matrix = best_compiler(6, predicate)
        atoms = [assignment for assignment in cube if predicate(assignment)]
        print(
            f"{name}: atoms={len(atoms)} order={order} "
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
            assert witness["coefficient"][0] == witness["target"][0] == 0
            print(
                f"  atom={atom}: left={witness['left']} right={witness['right']} "
                f"hard={witness['hard_form']}"
            )

    print(f"child-oriented frames={solved}/{total} kernels={kernels} hard_forms={forms}")
    assert solved == total == 20
    assert kernels == {symmetric_kernel_code()}
    assert forms == {(0, 1, 0, 0, 0, 0)}


if __name__ == "__main__":
    audit()
