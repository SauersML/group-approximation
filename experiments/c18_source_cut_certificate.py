#!/usr/bin/env python3
"""Build a sparse noncommutative certificate for the oriented C18 source cut.

Use six formal projection variables.  F is the sum of the 20 forbidden C18
atoms, S=P_0 or P_1 is the forward-source projection, and E is the sum of the
16 positive-residual atoms.  The Boolean identity F*S=E holds modulo only
projection idempotence and pairwise context commutators.  We reduce the free
polynomial F*S-E to sorted square-free normal form while recording every
adjacent swap and idempotence deletion, then reconstruct the input polynomial
from the resulting sparse relator-ideal certificate exactly over Z.
"""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
from itertools import product

Word = tuple[int, ...]
Polynomial = dict[Word, Fraction]
CertificateKey = tuple[str, int, int, Word, Word]


def add_term(poly: defaultdict[Word, Fraction], word: Word, coefficient: Fraction) -> None:
    poly[word] += coefficient
    if not poly[word]:
        del poly[word]


def add(left: Polynomial, right: Polynomial, scale: Fraction = Fraction(1)) -> Polynomial:
    out: defaultdict[Word, Fraction] = defaultdict(Fraction)
    for word, coefficient in left.items():
        add_term(out, word, coefficient)
    for word, coefficient in right.items():
        add_term(out, word, scale * coefficient)
    return dict(out)


def multiply(left: Polynomial, right: Polynomial) -> Polynomial:
    out: defaultdict[Word, Fraction] = defaultdict(Fraction)
    for left_word, left_coefficient in left.items():
        for right_word, right_coefficient in right.items():
            add_term(out, left_word + right_word, left_coefficient * right_coefficient)
    return dict(out)


def atom(assignment: tuple[int, ...]) -> Polynomial:
    polynomial: Polynomial = {(): Fraction(1)}
    for index, bit in enumerate(assignment):
        factor = {(index,): Fraction(1)}
        if not bit:
            factor = {(): Fraction(1), (index,): Fraction(-1)}
        polynomial = multiply(polynomial, factor)
    return polynomial


def even_phase(assignment: tuple[int, ...]) -> bool:
    return sum(assignment[3:]) % 2 == 0


def forbidden(assignment: tuple[int, ...]) -> bool:
    p, q, target, *_ = assignment
    return even_phase(assignment) and p + q != target


def positive_residual(assignment: tuple[int, ...]) -> bool:
    p, q, target, *_ = assignment
    return even_phase(assignment) and p + q - target > 0


def atom_sum(predicate) -> Polynomial:
    out: Polynomial = {}
    for assignment in product((0, 1), repeat=6):
        if predicate(assignment):
            out = add(out, atom(assignment))
    return out


def reduce_word(word: Word) -> tuple[Word, tuple[CertificateKey, ...]]:
    current = word
    certificate: list[CertificateKey] = []
    while True:
        inversion = next(
            (index for index in range(len(current) - 1) if current[index] > current[index + 1]),
            None,
        )
        if inversion is not None:
            index = inversion
            left, right = current[index], current[index + 1]
            prefix, suffix = current[:index], current[index + 2 :]
            certificate.append(("comm", left, right, prefix, suffix))
            current = prefix + (right, left) + suffix
            continue

        duplicate = next(
            (index for index in range(len(current) - 1) if current[index] == current[index + 1]),
            None,
        )
        if duplicate is not None:
            index = duplicate
            variable = current[index]
            prefix, suffix = current[:index], current[index + 2 :]
            certificate.append(("idem", variable, variable, prefix, suffix))
            current = prefix + (variable,) + suffix
            continue
        return current, tuple(certificate)


def reduce_polynomial(poly: Polynomial) -> tuple[Polynomial, dict[CertificateKey, Fraction]]:
    normal: defaultdict[Word, Fraction] = defaultdict(Fraction)
    certificate: defaultdict[CertificateKey, Fraction] = defaultdict(Fraction)
    for word, coefficient in poly.items():
        reduced, word_certificate = reduce_word(word)
        add_term(normal, reduced, coefficient)
        for key in word_certificate:
            certificate[key] += coefficient
            if not certificate[key]:
                del certificate[key]
    return dict(normal), dict(certificate)


def expand_certificate(certificate: dict[CertificateKey, Fraction]) -> Polynomial:
    out: defaultdict[Word, Fraction] = defaultdict(Fraction)
    for (kind, left, right, prefix, suffix), coefficient in certificate.items():
        if kind == "comm":
            add_term(out, prefix + (left, right) + suffix, coefficient)
            add_term(out, prefix + (right, left) + suffix, -coefficient)
        else:
            add_term(out, prefix + (left, left) + suffix, coefficient)
            add_term(out, prefix + (left,) + suffix, -coefficient)
    return dict(out)


def evaluate(poly: Polynomial, assignment: tuple[int, ...]) -> Fraction:
    total = Fraction(0)
    for word, coefficient in poly.items():
        value = 1
        for variable in word:
            value *= assignment[variable]
        total += coefficient * value
    return total


def audit() -> None:
    forbidden_polynomial = atom_sum(forbidden)
    exit_polynomial = atom_sum(positive_residual)
    source_polynomial: Polynomial = {
        (0,): Fraction(1),
        (1,): Fraction(1),
        (0, 1): Fraction(-1),
    }
    difference = add(multiply(forbidden_polynomial, source_polynomial), exit_polynomial, Fraction(-1))

    for assignment in product((0, 1), repeat=6):
        assert evaluate(difference, assignment) == 0

    normal, certificate = reduce_polynomial(difference)
    assert not normal
    assert expand_certificate(certificate) == difference

    commutators = {key: value for key, value in certificate.items() if key[0] == "comm"}
    idempotences = {key: value for key, value in certificate.items() if key[0] == "idem"}
    l1 = sum(abs(value) for value in certificate.values())
    max_context = max(len(key[3]) + 2 + len(key[4]) for key in certificate)
    print(f"expanded difference monomials={len(difference)}")
    print(
        f"certificate terms={len(certificate)} commutators={len(commutators)} "
        f"idempotences={len(idempotences)}"
    )
    print(f"certificate l1={l1} maximum word length={max_context}")


if __name__ == "__main__":
    audit()
