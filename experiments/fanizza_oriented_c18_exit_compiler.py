#!/usr/bin/env python3
"""Compile and audit the two oriented exits in Fanizza constraint C18.

On the even-phase carrier, C18 asserts p+q=r for three projection bits.
For the forward recurrence only positive residual matters.  The two Boolean
exit predicates

    e1 = [p+q-r > 0] and even_phase,
    e2 = [(p,q,r) = (1,1,0)] and even_phase

satisfy p+q <= r+e1+e2 and e1+e2 <= p+q pointwise.  The second copy exactly
records the multiplicity-two residual at 110.  This script verifies the
integer inequalities, builds compact Schur compilers, and searches the same
source-fixed symmetric rank-three frames used by the full Fanizza menu.
"""
from __future__ import annotations

from itertools import product

from fanizza_fixed_predicate_rank_compiler import best_compiler
from fanizza_partial_center_frame_search import (
    find_witness,
    symmetric_kernel_code,
)


def even_phase(bits: tuple[int, int, int]) -> bool:
    return sum(bits) % 2 == 0


def first_exit(assignment: tuple[int, ...]) -> bool:
    p, q, target, j, xzx, z = assignment
    return even_phase((j, xzx, z)) and p + q - target > 0


def second_exit(assignment: tuple[int, ...]) -> bool:
    p, q, target, j, xzx, z = assignment
    return even_phase((j, xzx, z)) and (p, q, target) == (1, 1, 0)


def original_c18_failure(assignment: tuple[int, ...]) -> bool:
    p, q, target, j, xzx, z = assignment
    return even_phase((j, xzx, z)) and p + q != target


def audit(maximum_weight: int = 2) -> None:
    cube = tuple(product((0, 1), repeat=6))
    oriented_occurrences = 0
    original_bad = 0
    source_local_bad = 0
    for assignment in cube:
        p, q, target, *_ = assignment
        e1 = int(first_exit(assignment))
        e2 = int(second_exit(assignment))
        phase = even_phase(assignment[3:])
        if phase:
            assert p + q <= target + e1 + e2
            assert e1 + e2 <= p + q
            assert p + q - target <= e1 + e2
        if original_c18_failure(assignment):
            original_bad += 1
            if p + q > 0:
                source_local_bad += 1
                assert e1 == 1
        if e1 or e2:
            assert original_c18_failure(assignment)
        oriented_occurrences += e1 + e2

    assert original_bad == 20
    assert source_local_bad == 16
    assert oriented_occurrences == 20
    print(
        "C18 integer ledger: original bad=20, source-local bad=16, "
        "oriented exit occurrences=20"
    )

    solved = 0
    total = 0
    kernels = set()
    forms = set()
    for name, predicate in (("positive-residual", first_exit), ("double-110", second_exit)):
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

    print(f"oriented frames={solved}/{total} kernels={kernels} hard_forms={forms}")
    assert solved == total == oriented_occurrences == 20
    assert kernels == {symmetric_kernel_code()}
    assert forms == {(0, 1, 0, 0, 0, 0)}


if __name__ == "__main__":
    audit()
