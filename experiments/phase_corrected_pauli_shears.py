#!/usr/bin/env python3
"""Verify opposite Pauli shears after adjoining a central fourth root.

Elements are R^r p^a q^b with r in Z/4 and a,b in F2.  Multiplication uses
q p = R^2 p q, so [p,q]=R^2 and p,q are involutions.  The maps

    p -> p,       q -> R p q
    p -> R p q,   q -> q

are the two opposite transvections on the F2 quotient.  The R phase makes
the image of the sheared generator an involution.
"""
from __future__ import annotations

from itertools import product

Element = tuple[int, int, int]
ELEMENTS: tuple[Element, ...] = tuple(product(range(4), (0, 1), (0, 1)))
R: Element = (1, 0, 0)
P: Element = (0, 1, 0)
Q: Element = (0, 0, 1)


def multiply(left: Element, right: Element) -> Element:
    r, a, b = left
    s, c, d = right
    return ((r + s + 2 * b * c) % 4, a ^ c, b ^ d)


def power(value: Element, exponent: int) -> Element:
    out = (0, 0, 0)
    for _ in range(exponent):
        out = multiply(out, value)
    return out


def inverse(value: Element) -> Element:
    return next(candidate for candidate in ELEMENTS if multiply(value, candidate) == (0, 0, 0) and multiply(candidate, value) == (0, 0, 0))


def commutator(left: Element, right: Element) -> Element:
    return multiply(multiply(multiply(left, right), inverse(left)), inverse(right))


def hom_from_images(value: Element, image_p: Element, image_q: Element) -> Element:
    r, a, b = value
    return multiply(power(R, r), multiply(power(image_p, a), power(image_q, b)))


def audit_map(image_p: Element, image_q: Element) -> tuple[Element, ...]:
    values = tuple(hom_from_images(value, image_p, image_q) for value in ELEMENTS)
    assert len(set(values)) == len(ELEMENTS)
    for left, right in product(ELEMENTS, repeat=2):
        assert hom_from_images(multiply(left, right), image_p, image_q) == multiply(
            hom_from_images(left, image_p, image_q),
            hom_from_images(right, image_p, image_q),
        )
    return values


def compose(left: tuple[Element, ...], right: tuple[Element, ...]) -> tuple[Element, ...]:
    index = {value: position for position, value in enumerate(ELEMENTS)}
    return tuple(left[index[value]] for value in right)


def audit() -> None:
    identity = tuple(ELEMENTS)
    assert power(R, 4) == (0, 0, 0)
    assert power(P, 2) == power(Q, 2) == (0, 0, 0)
    assert commutator(P, Q) == power(R, 2)

    diagonal = multiply(R, multiply(P, Q))
    assert power(diagonal, 2) == (0, 0, 0)
    shear_q = audit_map(P, diagonal)
    shear_p = audit_map(diagonal, Q)

    for shear in (shear_q, shear_p):
        square = compose(shear, shear)
        assert square == identity

    product_map = compose(shear_p, shear_q)
    current = identity
    order = next(
        exponent
        for exponent in range(1, 25)
        if (current := compose(product_map, current)) == identity
    )
    assert order == 3

    print("phase-Pauli group order=16")
    print("opposite phase-corrected shears are involutive automorphisms")
    print("their quotient actions are the two opposite GL2(F2) transvections")
    print(f"product automorphism order={order} (finite local shadow of the polynomial clock)")


if __name__ == "__main__":
    audit()
