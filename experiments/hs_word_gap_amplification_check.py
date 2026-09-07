#!/usr/bin/env python3
"""Exact finite replay of the scalar-sensitive HS word amplifier.

Uses only Python's standard library. This checks the amplifier identities on
explicit monomial unitary matrices and a finite rational grid, not the missing
all-dimensions relator gap for any group. Run from any directory; JSON is sent
to stdout. The mathematical proof is hs-word-gap-linearization-2026-09-07.md.
"""

from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
import json


def require(condition, message):
    if not condition:
        raise AssertionError(message)


@dataclass(frozen=True)
class Monomial:
    """A e_j = i**phase[j] e_perm[j], with exact Gaussian-unit entries."""

    perm: tuple
    phase: tuple

    def __post_init__(self):
        require(len(self.perm) > 0, "matrix dimension must be positive")
        require(sorted(self.perm) == list(range(len(self.perm))), "not a permutation")
        require(len(self.phase) == len(self.perm), "phase length mismatch")
        require(all(p in range(4) for p in self.phase), "invalid Gaussian unit")

    @property
    def dim(self):
        return len(self.perm)

    def __matmul__(self, other):
        require(self.dim == other.dim, "matrix size mismatch")
        return Monomial(
            tuple(self.perm[other.perm[j]] for j in range(self.dim)),
            tuple((other.phase[j] + self.phase[other.perm[j]]) % 4
                  for j in range(self.dim)),
        )

    def inverse(self):
        perm = [0] * self.dim
        phase = [0] * self.dim
        for j, p in enumerate(self.perm):
            perm[p] = j
            phase[p] = -self.phase[j] % 4
        return Monomial(tuple(perm), tuple(phase))

    def conjugate(self):
        return Monomial(self.perm, tuple(-p % 4 for p in self.phase))

    def trace(self):
        real, imag = (1, 0, -1, 0), (0, 1, 0, -1)
        fixed = [j for j in range(self.dim) if self.perm[j] == j]
        return (Q(sum(real[self.phase[j]] for j in fixed), self.dim),
                Q(sum(imag[self.phase[j]] for j in fixed), self.dim))

    def hs_energy(self):
        # Independently sum squared column distances ||A e_j-e_j||^2/d.
        diagonal = (0, 2, 4, 2)
        return Q(sum(diagonal[self.phase[j]] if self.perm[j] == j else 2
                     for j in range(self.dim)), self.dim)


def identity(d):
    return Monomial(tuple(range(d)), (0,) * d)


def direct_sum(*blocks):
    perm, phase, offset = [], [], 0
    for a in blocks:
        perm.extend(offset + j for j in a.perm)
        phase.extend(a.phase)
        offset += a.dim
    return Monomial(tuple(perm), tuple(phase))


def tensor(a, b):
    return Monomial(
        tuple(i * b.dim + j for i in a.perm for j in b.perm),
        tuple((p + q) % 4 for p in a.phase for q in b.phase),
    )


def tensor_power(a, k):
    require(k >= 0, "negative tensor exponent")
    out = identity(1)
    for _ in range(k):
        out = tensor(out, a)
    return out


def symmetrize(a):
    return direct_sum(a, a.conjugate(), identity(a.dim), identity(a.dim))


def evaluate(generators, word):
    out = identity(generators[0].dim)
    for letter in word:
        a = generators[abs(letter) - 1]
        out = out @ (a if letter > 0 else a.inverse())
    return out


def reduced_words():
    yield ()
    letters = (-3, -2, -1, 1, 2, 3)
    for length in range(1, 4):
        for word in product(letters, repeat=length):
            if all(word[j] != -word[j + 1] for j in range(length - 1)):
                yield word


def matrix_checks():
    x = Monomial((1, 0), (0, 0))
    y = Monomial((0, 1), (1, 0))
    z = Monomial((0, 1), (1, 1))
    generators = (x, y, z)
    require(x @ y != y @ x, "fixture must be noncommuting")
    require(evaluate(generators, (1, 2, -1, -2)) != identity(2),
            "commutator fixture is trivial")
    for a in generators:
        require(a @ a.inverse() == identity(a.dim), "inverse failure")
    # A projective conjugate tensor erases this scalar; the new transform does not.
    require(tensor(z, z.conjugate()) == identity(4), "scalar control failure")
    require(symmetrize(z).hs_energy() == 1, "lost scalar i")
    minus = Monomial((0, 1), (2, 2))
    require(symmetrize(minus).hs_energy() == 2, "lost scalar minus one")

    words = list(reduced_words())
    checks = 0
    maximum_dimension = 0
    for padding, exponents in ((0, (1, 2, 3)), (3, (1, 2))):
        base = generators if padding == 0 else tuple(
            direct_sum(a, identity(padding)) for a in generators)
        for k in exponents:
            amplified = tuple(tensor_power(symmetrize(a), k) for a in base)
            maximum_dimension = max(maximum_dimension, amplified[0].dim)
            for word in words:
                original = evaluate(base, word)
                actual = evaluate(amplified, word)
                expected_matrix = tensor_power(symmetrize(original), k)
                require(actual == expected_matrix, "word transform is not functorial")
                energy = original.hs_energy()
                require(energy == 2 - 2 * original.trace()[0], "HS/trace mismatch")
                require(symmetrize(original).trace() == (1 - energy / 4, Q(0)),
                        "real trace identity failed")
                expected_energy = 2 * (1 - (1 - energy / 4) ** k)
                require(actual.hs_energy() == expected_energy, "tensor energy failed")
                require(actual.hs_energy() <= Q(k, 2) * energy, "relator error grew")
                if padding:
                    raw_energy = evaluate(generators, word).hs_energy()
                    require(energy == Q(2, 2 + padding) * raw_energy,
                            "wrong dimension normalization after padding")
                checks += 1
    return {"words": len(words), "explicit_word_tensor_checks": checks,
            "maximum_materialized_dimension": maximum_dimension,
            "noncommuting_and_scalar_phase_controls": "passed"}


def rational_checks():
    checks = 0
    error_checks = 0
    for denominator in range(1, 65):
        for numerator in range(1, denominator + 1):
            t = Q(numerator, denominator)
            k = (denominator + numerator - 1) // numerator
            a = 4 * t
            require(k * t >= 1, "ceiling lower bound failed")
            require(k * a <= 8, "ceiling upper bound failed")
            require((1 - t) ** k <= 1 / (1 + k * t), "reciprocal Bernoulli failed")
            require(2 * (1 - (1 - t) ** k) >= 1, "marked word did not separate")
            for relator_energy in (Q(0), Q(1, 16), Q(1), Q(2), Q(4)):
                amplified_energy = 2 * (1 - (1 - relator_energy / 4) ** k)
                require(amplified_energy <= Q(k, 2) * relator_energy,
                        "Bernoulli error bound failed")
                require(Q(k, 2) * relator_energy <= 4 * relator_energy / a,
                        "linearization constant failed")
                error_checks += 1
            checks += 1
    return {"rational_mark_checks": checks, "rational_relator_checks": error_checks,
            "zero_mark": "linear inequality is immediate; no exponent is chosen"}


def main():
    result = {
        "schema_version": 1,
        "arithmetic": "exact integers and fractions.Fraction",
        "matrix_replay": matrix_checks(),
        "scalar_replay": rational_checks(),
        "scope": "Finite replay of amplifier identities and bounds only.",
        "group_specific_gap_established": False,
        "nonhyperlinear_group_constructed": False,
        "lean_verified": False,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
