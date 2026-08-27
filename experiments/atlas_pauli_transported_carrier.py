"""Audit the comb-transported Pauli carrier against the raw branch cell.

The calculation is exact in the binary Leavitt prefix algebra.  It asks
whether the involution defining the transported carrier stays in a small
finite subgroup with the parent/cylinder Pauli signs.  A finite closure would
show that no additional support information is present there; escape names
the first genuinely cross-chart operation.
"""

import json
import sys
import collections

sys.path.insert(0, "experiments")

from atlas_raw_branch_pauli_cell import (  # noqa: E402
    element_order,
    equal,
    generated_subgroup,
    order_histogram,
    root,
)
from atlas_raw_compressor_proper_infinite import (  # noqa: E402
    product,
    raw_and_comb,
    s,
    t,
)
from atlas_survivor_prefix_obstruction import (  # noqa: E402
    cylinder_projection,
    leavitt_star,
)


def commute(left, right):
    return equal(product(left, right), product(right, left))


def intersection_size(left, right):
    return sum(1 for value in left
               if any(equal(value, other) for other in right))


def intersection_elements(left, right):
    return [value for value in left
            if any(equal(value, other) for other in right)]


def generated_subgroup_with_words(generators, limit=128):
    elements = [(product(), ())]
    queue = collections.deque([(product(), ())])
    while queue:
        left, word = queue.popleft()
        for index, generator in enumerate(generators):
            value = product(left, generator)
            if not any(equal(value, old) for old, _ in elements):
                entry = (value, word + (index,))
                elements.append(entry)
                queue.append(entry)
                if len(elements) > limit:
                    raise AssertionError("subgroup exceeded word audit limit")
    return elements


def main():
    raw, comb = raw_and_comb()
    z11 = root(cylinder_projection("11"))
    z001 = root(cylinder_projection("001"))
    c11 = product(raw, z11, raw, z11)
    transported = product(leavitt_star(comb), z001, comb)

    pair_orders = {
        "transported": element_order(transported, 128),
        "transported_times_z11": element_order(
            product(transported, z11), 128),
        "transported_times_z001": element_order(
            product(transported, z001), 128),
        "transported_times_c11": element_order(
            product(transported, c11), 128),
    }
    commutation = {
        "with_raw": commute(transported, raw),
        "with_z11": commute(transported, z11),
        "with_z001": commute(transported, z001),
        "with_c11": commute(transported, c11),
    }

    parent_cell = generated_subgroup((raw, z11, z001), limit=32)
    transported_parent_cell = [
        product(leavitt_star(comb), value, comb) for value in parent_cell
    ]
    p0 = product(s(0), t(0))
    p1 = product(s(1), t(1))
    x0 = root(p0, 0, 1)
    y0 = root(p0, 1, 2)
    z1 = root(p1)
    two_pauli_cell = generated_subgroup((x0, y0, raw, z1), limit=128)
    two_pauli_words = generated_subgroup_with_words(
        (x0, y0, raw, z1), limit=128)
    transported_two_pauli_cell = [
        product(leavitt_star(comb), value, comb)
        for value in two_pauli_cell
    ]
    two_pauli_intersection = intersection_elements(
        two_pauli_cell, transported_two_pauli_cell)
    nontrivial_two_pauli_intersection = next(
        value for value in two_pauli_intersection
        if element_order(value) != 1
    )
    intersection_word = next(
        word for value, word in two_pauli_words
        if equal(value, nontrivial_two_pauli_intersection)
    )
    transported_preimage_word = next(
        word for value, word in two_pauli_words
        if equal(
            product(leavitt_star(comb), value, comb),
            nontrivial_two_pauli_intersection,
        )
    )
    z0 = product(x0, y0, x0, y0)
    c1 = product(raw, z1, raw, z1)

    finite_closure = None
    closure_status = "exceeded_64"
    try:
        finite_closure = generated_subgroup(
            (raw, z11, z001, transported), limit=64)
        closure_status = "finite"
    except AssertionError:
        pass

    result = {
        "transported_sign": "u* x_13(p_001) u",
        "pair_orders_up_to_128": pair_orders,
        "commutation": commutation,
        "parent_cell_order": len(parent_cell),
        "transported_outside_parent_cell": not any(
            equal(transported, value) for value in parent_cell),
        "parent_cell_intersection_with_comb_conjugate": intersection_size(
            parent_cell, transported_parent_cell),
        "two_pauli_cell_order": len(two_pauli_cell),
        "two_pauli_cell_intersection_with_comb_conjugate": intersection_size(
            two_pauli_cell, transported_two_pauli_cell),
        "nontrivial_two_pauli_intersection": {
            "order": element_order(nontrivial_two_pauli_intersection),
            "is_z0": equal(nontrivial_two_pauli_intersection, z0),
            "is_raw_z1_commutator": equal(
                nontrivial_two_pauli_intersection, c1),
            "is_product_of_two_central_commutators": equal(
                nontrivial_two_pauli_intersection, product(z0, c1)),
            "is_x13_one": equal(
                nontrivial_two_pauli_intersection, product(z0, z1)),
            "word_in_x0_y0_raw_z1": list(intersection_word),
            "comb_conjugate_preimage_word": list(transported_preimage_word),
            "commutes_with_two_pauli_cell": all(
                commute(nontrivial_two_pauli_intersection, value)
                for value in two_pauli_cell
            ),
        },
        "closure_status": closure_status,
        "closure_order": None if finite_closure is None else len(finite_closure),
        "closure_order_histogram": (
            None if finite_closure is None else order_histogram(finite_closure)
        ),
        "closure_structure": "D8 times C2 times C2",
    }
    expected = {
        "transported_sign": "u* x_13(p_001) u",
        "pair_orders_up_to_128": {
            "transported": 2,
            "transported_times_z11": 2,
            "transported_times_z001": 2,
            "transported_times_c11": 2,
        },
        "commutation": {
            "with_raw": True,
            "with_z11": True,
            "with_z001": True,
            "with_c11": True,
        },
        "parent_cell_order": 16,
        "transported_outside_parent_cell": True,
        "parent_cell_intersection_with_comb_conjugate": 1,
        "two_pauli_cell_order": 64,
        "two_pauli_cell_intersection_with_comb_conjugate": 2,
        "nontrivial_two_pauli_intersection": {
            "order": 2,
            "is_z0": False,
            "is_raw_z1_commutator": False,
            "is_product_of_two_central_commutators": False,
            "is_x13_one": True,
            "word_in_x0_y0_raw_z1": [0, 1, 0, 1, 3],
            "comb_conjugate_preimage_word": [0, 1, 0, 1],
            "commutes_with_two_pauli_cell": False,
        },
        "closure_status": "finite",
        "closure_order": 32,
        "closure_order_histogram": {1: 1, 2: 23, 4: 8},
        "closure_structure": "D8 times C2 times C2",
    }
    if result != expected:
        raise AssertionError(result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
