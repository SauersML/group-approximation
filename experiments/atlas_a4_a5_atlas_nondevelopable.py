#!/usr/bin/env python3
"""Exact incompatibility of the A5 rectangle with the marked S3^2/S4 seam.

The balanced 720-dimensional atlas selected one faithful A5 completion of
the large K2,2 rectangle.  In that A5 the two marked S3 subgroups intersect
in d=r^-1*u*r=t^-1*s*t.  The first packet F=S3xS3 makes c commute with d,
whereas the marked collision S4 does not: imposing that commutator kills its
normal Klein four, including c.  Hence those three finite vertices have no
faithful common completion.
"""

from __future__ import annotations

import json


def mul(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    """GAP permutation product: x^(left*right)=(x^left)^right."""
    return tuple(right[left[x]] for x in range(len(left)))


def inv(value: tuple[int, ...]) -> tuple[int, ...]:
    out = [0] * len(value)
    for source, target in enumerate(value):
        out[target] = source
    return tuple(out)


def cycle(size: int, *cycles: tuple[int, ...]) -> tuple[int, ...]:
    value = list(range(size))
    for cyc in cycles:
        for old, new in zip(cyc, cyc[1:] + cyc[:1]):
            value[old] = new
    return tuple(value)


def generated(*generators: tuple[int, ...]) -> frozenset[tuple[int, ...]]:
    identity = tuple(range(len(generators[0])))
    seen = {identity}
    todo = [identity]
    moves = generators + tuple(inv(g) for g in generators)
    while todo:
        old = todo.pop()
        for move in moves:
            new = mul(old, move)
            if new not in seen:
                seen.add(new)
                todo.append(new)
    return frozenset(seen)


def commutator(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    return mul(mul(mul(inv(left), inv(right)), left), right)


def main() -> None:
    # F=S3xS3 on two disjoint triples.
    r_f = cycle(6, (0, 1, 2))
    u_f = cycle(6, (1, 2))
    c_f = cycle(6, (4, 5))
    d_f = mul(mul(inv(r_f), u_f), r_f)
    f_group = generated(r_f, u_f, c_f, cycle(6, (3, 4, 5)))
    assert len(f_group) == 36
    assert commutator(c_f, d_f) == tuple(range(6))
    assert len(generated(c_f, d_f)) == 4

    # L=A5 from the frozen full-large K2,2 certificate.
    r_l = (0, 1, 3, 4, 2)
    y_l = (1, 2, 0, 3, 4)
    u_l = (1, 0, 3, 2, 4)
    b_l = (2, 1, 0, 4, 3)
    t_l = inv(y_l)
    s_l = mul(b_l, inv(t_l))
    d_l_left = mul(mul(inv(r_l), u_l), r_l)
    d_l_right = mul(mul(inv(t_l), s_l), t_l)
    l_group = generated(r_l, u_l, t_l, s_l)
    assert len(l_group) == 60
    assert len(generated(r_l, u_l)) == len(generated(t_l, s_l)) == 6
    assert generated(r_l, u_l) & generated(t_l, s_l) == generated(d_l_left)
    assert d_l_left == d_l_right

    # J=S4 from the exact collision-19243 calibration.
    t_j = cycle(4, (0, 1, 2))
    s_j = cycle(4, (0, 1))
    c_j = cycle(4, (0, 2), (1, 3))
    d_j = mul(mul(inv(t_j), s_j), t_j)
    j_group = generated(t_j, s_j, c_j)
    collision = commutator(c_j, d_j)
    collision_normal_closure = generated(*(
        mul(mul(inv(g), collision), g) for g in j_group
    ))
    assert len(j_group) == 24
    assert len(generated(c_j, d_j)) == 8
    assert collision != tuple(range(4))
    assert len(generated(collision)) == 2
    assert len(collision_normal_closure) == 4
    assert c_j in collision_normal_closure

    print(json.dumps({
        "A5_order": len(l_group),
        "A5_radial_S3_intersection_order": 2,
        "transported_overlap": "d=r^-1*u*r=t^-1*s*t",
        "F_order": len(f_group),
        "F_relation": "[c,d]=1",
        "J_order": len(j_group),
        "J_cd_subgroup_order": len(generated(c_j, d_j)),
        "J_commutator_nontrivial": True,
        "J_commutator_normal_closure_order": len(collision_normal_closure),
        "J_commutator_normal_closure_contains_c": True,
        "conclusion": "the marked A5, S3xS3, and collision S4 vertices have no faithful common completion",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
