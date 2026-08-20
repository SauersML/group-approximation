#!/usr/bin/env python3
"""Verify the finite quotient wall for y -> x*y over F_2[x,y].

The quotient x^2=x, y^2=y, xy=0 is F_2^3, evaluated at
(0,0), (1,0), (0,1).  The compressor sends (a,b,c) to (a,b,a).
"""
from __future__ import annotations

from itertools import product


def sigma_on_evaluations(values: tuple[int, int, int]) -> tuple[int, int, int]:
    at_00, at_10, _at_01 = values
    return at_00, at_10, at_00


def audit() -> None:
    ring = list(product((0, 1), repeat=3))
    image = {sigma_on_evaluations(value) for value in ring}
    expected = {(a, b, a) for a, b in product((0, 1), repeat=2)}
    assert image == expected

    order_g = (2**3 - 1) * (2**3 - 2) * (2**3 - 2**2)
    assert order_g == 168  # GL_3(F_2)=SL_3(F_2).
    order_b = order_g**3
    order_a = order_g**2
    index = order_b // order_a
    assert index == order_g

    # On l2(B), dim lambda(B)'=|B|. Restriction to A is [B:A]
    # regular A copies, so dim lambda(A)'=[B:A]*|B|.
    commutant_b = order_b
    commutant_a = index * order_b
    wall_rank = commutant_a - commutant_b
    assert wall_rank == (index - 1) * order_b

    print(f"ring size=8 compressed subring size={len(image)}")
    print(f"|G|={order_g} |B|={order_b} |A|={order_a} [B:A]={index}")
    print(f"regular adjoint wall density={wall_rank}/{order_b**2}")


if __name__ == "__main__":
    audit()
