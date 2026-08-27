#!/usr/bin/env python3
"""Exact canonical free-product obstruction for an OR3 Fano cap.

Let A=C_2^3, let q be the four-character Fano-cap projection associated to
one nonzero parity row, and let t be the generator of a free C_2 factor.
Inside Q[A*C_2] the script computes

    tau(q)=1/2,
    tau(t q t q)=1/4,
    ||[t,q]||_2^2=1/2.

The implementation is a small exact group-algebra reducer.  It is independent
of floating-point linear algebra and also checks the eight-character Fourier
definition of q against the closed form (1-a_lambda)/2.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product


Bits = tuple[int, int, int]
Factor = tuple[str, Bits | None]
Word = tuple[Factor, ...]
Algebra = dict[Word, Fraction]

ZERO_BITS: Bits = (0, 0, 0)
ONE = Fraction(1)


def xor(left: Bits, right: Bits) -> Bits:
    return tuple(a ^ b for a, b in zip(left, right))  # type: ignore[return-value]


def reduce_word(factors: Word) -> Word:
    stack: list[Factor] = []
    for kind, value in factors:
        if kind == "A" and value == ZERO_BITS:
            continue
        if stack and stack[-1][0] == kind:
            previous_kind, previous_value = stack.pop()
            if kind == "T":
                continue
            assert previous_value is not None and value is not None
            combined = xor(previous_value, value)
            if combined != ZERO_BITS:
                stack.append(("A", combined))
        else:
            stack.append((kind, value))
    return tuple(stack)


def add_term(algebra: Algebra, word: Word, coefficient: Fraction) -> None:
    word = reduce_word(word)
    algebra[word] = algebra.get(word, Fraction(0)) + coefficient
    if algebra[word] == 0:
        del algebra[word]


def multiply(left: Algebra, right: Algebra) -> Algebra:
    result: Algebra = {}
    for left_word, left_coefficient in left.items():
        for right_word, right_coefficient in right.items():
            add_term(
                result,
                left_word + right_word,
                left_coefficient * right_coefficient,
            )
    return result


def adjoint(algebra: Algebra) -> Algebra:
    result: Algebra = {}
    for word, coefficient in algebra.items():
        # Every factor is an involution, so only the order reverses.
        add_term(result, tuple(reversed(word)), coefficient)
    return result


def add(left: Algebra, right: Algebra, right_scale: Fraction = ONE) -> Algebra:
    result = dict(left)
    for word, coefficient in right.items():
        add_term(result, word, right_scale * coefficient)
    return result


def canonical_trace(algebra: Algebra) -> Fraction:
    return algebra.get((), Fraction(0))


def a_word(bits: Bits) -> Word:
    return () if bits == ZERO_BITS else (("A", bits),)


T: Algebra = {(("T", None),): ONE}


def character_projection(character: Bits) -> Algebra:
    result: Algebra = {}
    for group_element in product((0, 1), repeat=3):
        bits: Bits = group_element
        parity = sum(a * b for a, b in zip(character, bits)) % 2
        add_term(result, a_word(bits), Fraction((-1) ** parity, 8))
    return result


LAMBDA: Bits = (1, 1, 1)
CAP = {
    character
    for character in product((0, 1), repeat=3)
    if sum(a * b for a, b in zip(LAMBDA, character)) % 2 == 1
}

Q: Algebra = {}
for character in CAP:
    Q = add(Q, character_projection(character))

Q_CLOSED: Algebra = {
    (): Fraction(1, 2),
    a_word(LAMBDA): Fraction(-1, 2),
}
assert Q == Q_CLOSED
assert multiply(Q, Q) == Q
assert adjoint(Q) == Q

TQTQ = multiply(T, multiply(Q, multiply(T, Q)))
COMMUTATOR = add(multiply(T, Q), multiply(Q, T), Fraction(-1))
COMMUTATOR_SQUARE = multiply(adjoint(COMMUTATOR), COMMUTATOR)

assert canonical_trace(Q) == Fraction(1, 2)
assert canonical_trace(TQTQ) == Fraction(1, 4)
assert canonical_trace(COMMUTATOR_SQUARE) == Fraction(1, 2)


def main() -> None:
    print("group=C2^3*C2")
    print("cap_characters=4")
    print("q=(1-a_111)/2")
    print(f"canonical_trace_q={canonical_trace(Q)}")
    print(f"canonical_trace_tqtq={canonical_trace(TQTQ)}")
    print(f"canonical_commutator_hs2={canonical_trace(COMMUTATOR_SQUARE)}")


if __name__ == "__main__":
    main()
