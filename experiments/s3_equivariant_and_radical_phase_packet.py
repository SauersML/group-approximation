#!/usr/bin/env python3
"""Audit the S3-equivariant phase-root packet for a binary AND violation.

The alternating commutator form is H tensor [[x,1],[1,y]], where H is the
two-dimensional hyperbolic form.  Its rank is four except at x=y=1, where
the radical is the natural two-dimensional GL2(F2)=S3 module.  Central fourth
roots of J,z_x,z_y repair the quadratic refinement, lifting the two opposite
transvections of the first tensor factor to involutive group automorphisms.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import product

Center = tuple[int, int, int]
Vector = tuple[int, int, int, int]
ZERO_CENTER: Center = (0, 0, 0)
ZERO_VECTOR: Vector = (0, 0, 0, 0)


def center_add(left: Center, right: Center) -> Center:
    return tuple((a + b) % 4 for a, b in zip(left, right))


def center_negate(value: Center) -> Center:
    return tuple((-entry) % 4 for entry in value)


def coefficient_add(left: Center, right: Center) -> Center:
    return tuple(a ^ b for a, b in zip(left, right))


def coefficient_scale_two(value: Center) -> Center:
    return tuple(2 * (entry & 1) for entry in value)


J_COEFFICIENT: Center = (1, 0, 0)
X_COEFFICIENT: Center = (0, 1, 0)
Y_COEFFICIENT: Center = (0, 0, 1)


def form_entry(left: int, right: int) -> Center:
    if left == right or left // 2 == right // 2:
        return ZERO_CENTER
    mu, nu = left % 2, right % 2
    if mu == nu == 0:
        return X_COEFFICIENT
    if mu == nu == 1:
        return Y_COEFFICIENT
    return J_COEFFICIENT


def cocycle(left: Vector, right: Vector) -> Center:
    out = ZERO_CENTER
    for high in range(4):
        for low in range(high):
            if left[high] and right[low]:
                out = coefficient_add(out, form_entry(high, low))
    return out


@dataclass(frozen=True)
class Element:
    roots: Center
    vector: Vector


IDENTITY = Element(ZERO_CENTER, ZERO_VECTOR)
ROOTS = tuple(Element(tuple(1 if i == j else 0 for i in range(3)), ZERO_VECTOR) for j in range(3))
GENERATORS = tuple(Element(ZERO_CENTER, tuple(1 if i == j else 0 for i in range(4))) for j in range(4))


def multiply(left: Element, right: Element) -> Element:
    correction = coefficient_scale_two(cocycle(left.vector, right.vector))
    return Element(
        center_add(center_add(left.roots, right.roots), correction),
        tuple(a ^ b for a, b in zip(left.vector, right.vector)),
    )


def power(value: Element, exponent: int) -> Element:
    out = IDENTITY
    for _ in range(exponent):
        out = multiply(out, value)
    return out


def inverse(value: Element) -> Element:
    square_correction = coefficient_scale_two(cocycle(value.vector, value.vector))
    return Element(
        center_negate(center_add(value.roots, square_correction)),
        value.vector,
    )


def commutator(left: Element, right: Element) -> Element:
    return multiply(multiply(multiply(left, right), inverse(left)), inverse(right))


def transvection(kind: str, vector: Vector) -> Vector:
    out = list(vector)
    for mu in range(2):
        first, second = mu, 2 + mu
        if kind == "upper":
            out[first] ^= vector[second]
        elif kind == "lower":
            out[second] ^= vector[first]
        else:
            raise ValueError(kind)
    return tuple(out)


class Lift:
    def __init__(self, kind: str) -> None:
        self.kind = kind
        self.root_images = tuple(Element(center_negate(root.roots), ZERO_VECTOR) for root in ROOTS)
        self.generator_images = tuple(self._image_generator(index) for index in range(4))

    def _image_generator(self, index: int) -> Element:
        vector = transvection(self.kind, GENERATORS[index].vector)
        phase = cocycle(vector, vector)
        return Element(phase, vector)

    def __call__(self, value: Element) -> Element:
        out = IDENTITY
        for index, exponent in enumerate(value.roots):
            out = multiply(out, power(self.root_images[index], exponent))
        for index, bit in enumerate(value.vector):
            if bit:
                out = multiply(out, self.generator_images[index])
        return out

    def audit(self) -> None:
        for root, image in zip(ROOTS, self.root_images):
            assert power(image, 4) == IDENTITY
            assert self(self(root)) == root
        for generator, image in zip(GENERATORS, self.generator_images):
            assert power(image, 2) == IDENTITY
            assert self(self(generator)) == generator
        for left, right in product(GENERATORS, repeat=2):
            assert self(commutator(left, right)) == commutator(self(left), self(right))


def compose(left: Lift, right: Lift, value: Element) -> Element:
    return left(right(value))


def evaluated_form(x: int, y: int) -> list[list[int]]:
    coefficients = (1, x, y)
    return [
        [
            sum(coefficient * bit for coefficient, bit in zip(coefficients, form_entry(i, j))) & 1
            for j in range(4)
        ]
        for i in range(4)
    ]


def rank_f2(matrix: list[list[int]]) -> int:
    rows = [row[:] for row in matrix]
    rank = 0
    for column in range(len(rows[0])):
        pivot = next((row for row in range(rank, len(rows)) if rows[row][column]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for row in range(len(rows)):
            if row != rank and rows[row][column]:
                rows[row] = [a ^ b for a, b in zip(rows[row], rows[rank])]
        rank += 1
    return rank


def audit() -> None:
    profile = {(x, y): rank_f2(evaluated_form(x, y)) for x, y in product((0, 1), repeat=2)}
    assert profile == {(0, 0): 4, (0, 1): 4, (1, 0): 4, (1, 1): 2}

    upper = Lift("upper")
    lower = Lift("lower")
    upper.audit()
    lower.audit()
    test_generators = ROOTS + GENERATORS
    values = test_generators
    for _ in range(3):
        values = tuple(compose(upper, lower, value) for value in values)
    assert values == test_generators

    hot_radical = ((1, 1, 0, 0), (0, 0, 1, 1))
    nonzero = {hot_radical[0], hot_radical[1], tuple(a ^ b for a, b in zip(*hot_radical))}
    for lift in (upper, lower):
        images = {transvection(lift.kind, value) for value in nonzero}
        assert images == nonzero

    print(f"rank profile={profile}")
    print("central fourth roots of J,z_x,z_y lift both transvections involutively")
    print("their product has order three")
    print("the hot radical is the natural S3-module with one orbit of three nonzero words")


if __name__ == "__main__":
    audit()
