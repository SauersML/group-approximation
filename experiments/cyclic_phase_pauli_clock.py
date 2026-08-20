#!/usr/bin/env python3
"""Audit phase-corrected opposite polynomial shears on cyclic Weyl tapes.

For R_m=F_2[x]/(x^m-1), put V_m=R_m^2 and

    <(a,b),(c,d)> = [x^0](a d+b c).

The phase-Pauli group has normal forms R^r P(a)Q(b), R^4=1, and cocycle
2[x^0](b c).  The opposite polynomial shears

    U(a,b)=(a+x b,b),       L(a,b)=(a,b+x a)

are symplectic involutions.  This script constructs their lifts which invert
R, chooses the unique generator phases making the images involutions, audits
the full presentation on generators, and measures the order of the resulting
clock U L in the quotient and in the phase-Pauli automorphism group.

No large matrix group is enumerated: the audit is polynomial in m and is
intended to expose whether the local order-16 phenomenon survives growing
cyclic polynomial quotients.
"""
from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Pauli:
    phase: int
    p: int
    q: int


def rotate_x(value: int, width: int) -> int:
    mask = (1 << width) - 1
    return ((value << 1) & mask) | (value >> (width - 1))


def frobenius_pair(left: int, right: int, width: int) -> int:
    """Constant coefficient of left*right modulo x^width-1."""
    out = 0
    for index in range(width):
        out ^= ((left >> index) & 1) & ((right >> ((-index) % width)) & 1)
    return out


def multiply(left: Pauli, right: Pauli, width: int) -> Pauli:
    crossing = frobenius_pair(left.q, right.p, width)
    return Pauli(
        (left.phase + right.phase + 2 * crossing) % 4,
        left.p ^ right.p,
        left.q ^ right.q,
    )


def power(value: Pauli, exponent: int, width: int) -> Pauli:
    out = Pauli(0, 0, 0)
    for _ in range(exponent):
        out = multiply(out, value, width)
    return out


def inverse(value: Pauli, width: int) -> Pauli:
    square_phase = 2 * frobenius_pair(value.p, value.q, width)
    return Pauli((-value.phase - square_phase) % 4, value.p, value.q)


def commutator(left: Pauli, right: Pauli, width: int) -> Pauli:
    return multiply(
        multiply(multiply(left, right, width), inverse(left, width), width),
        inverse(right, width),
        width,
    )


def quotient_shear(kind: str, p: int, q: int, width: int) -> tuple[int, int]:
    if kind == "upper":
        return p ^ rotate_x(q, width), q
    if kind == "lower":
        return p, q ^ rotate_x(p, width)
    raise ValueError(kind)


class Lift:
    def __init__(self, kind: str, width: int) -> None:
        self.kind = kind
        self.width = width
        self.image_r = Pauli(3, 0, 0)
        self.image_p = tuple(self._generator_image(1 << index, 0) for index in range(width))
        self.image_q = tuple(self._generator_image(0, 1 << index) for index in range(width))

    def _generator_image(self, p: int, q: int) -> Pauli:
        out_p, out_q = quotient_shear(self.kind, p, q, self.width)
        # R times an order-four Weyl word is an involution.  The parity below
        # is exactly the quadratic-refinement correction.
        phase = frobenius_pair(out_p, out_q, self.width)
        return Pauli(phase, out_p, out_q)

    def __call__(self, value: Pauli) -> Pauli:
        out = power(self.image_r, value.phase, self.width)
        for index in range(self.width):
            if (value.p >> index) & 1:
                out = multiply(out, self.image_p[index], self.width)
        for index in range(self.width):
            if (value.q >> index) & 1:
                out = multiply(out, self.image_q[index], self.width)
        return out

    def generators(self) -> tuple[Pauli, ...]:
        return (Pauli(1, 0, 0),) + tuple(
            Pauli(0, 1 << index, 0) for index in range(self.width)
        ) + tuple(Pauli(0, 0, 1 << index) for index in range(self.width))

    def audit(self) -> None:
        generators = self.generators()
        images = tuple(self(value) for value in generators)
        assert power(images[0], 4, self.width) == Pauli(0, 0, 0)
        for image in images[1:]:
            assert power(image, 2, self.width) == Pauli(0, 0, 0)
        for i, left in enumerate(generators[1:]):
            for j, right in enumerate(generators[1:]):
                expected = self(commutator(left, right, self.width))
                got = commutator(images[i + 1], images[j + 1], self.width)
                assert got == expected
        for generator in generators:
            assert self(self(generator)) == generator


def compose(left: Lift, right: Lift, value: Pauli) -> Pauli:
    return left(right(value))


def automorphism_order(upper: Lift, lower: Lift, maximum: int) -> int | None:
    generators = upper.generators()
    values = generators
    for exponent in range(1, maximum + 1):
        values = tuple(compose(upper, lower, value) for value in values)
        if values == generators:
            return exponent
    return None


def quotient_clock_order(width: int, maximum: int) -> int | None:
    generators = tuple((1 << index, 0) for index in range(width)) + tuple(
        (0, 1 << index) for index in range(width)
    )
    values = generators
    for exponent in range(1, maximum + 1):
        values = tuple(
            quotient_shear(
                "upper",
                *quotient_shear("lower", p, q, width),
                width,
            )
            for p, q in values
        )
        if values == generators:
            return exponent
    return None


def audit(max_width: int = 12) -> None:
    print("m quotient_order lifted_order")
    for width in range(1, max_width + 1):
        upper = Lift("upper", width)
        lower = Lift("lower", width)
        upper.audit()
        lower.audit()
        quotient_order = quotient_clock_order(width, 200_000)
        lifted_order = automorphism_order(upper, lower, 400_000)
        assert quotient_order is not None
        assert lifted_order is not None
        assert lifted_order % quotient_order == 0
        print(width, quotient_order, lifted_order)


if __name__ == "__main__":
    audit()
