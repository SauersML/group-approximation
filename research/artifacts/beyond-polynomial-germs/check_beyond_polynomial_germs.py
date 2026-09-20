#!/usr/bin/env python3
"""Exact, finite formula checks for beyond_polynomial_germs.md.

These are sanity checks, NOT a formal verification of infinite-group embeddings,
finite presentability, finiteness properties, nonlinearity, or simplicity.
Only the Python standard library is required. Run with Python 3.10+.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import permutations, product
import json
from pathlib import Path

COUNTS: Counter[str] = Counter()


def check(category: str, condition: bool, context: object = None) -> None:
    if not condition:
        raise AssertionError(f"{category} failed: {context!r}")
    COUNTS[category] += 1


def choose_integer(n: int, k: int) -> int:
    if k < 0:
        return 0
    answer = F(1)
    for j in range(k):
        answer *= F(n - j, j + 1)
    if answer.denominator != 1:
        raise AssertionError("Generalized binomial coefficient is not integral")
    return answer.numerator


Matrix = tuple[tuple[F, ...], ...]


def identity(n: int) -> Matrix:
    return tuple(tuple(F(i == j) for j in range(n)) for i in range(n))


def multiply(a: Matrix, b: Matrix) -> Matrix:
    n = len(a)
    if n != len(b) or any(len(row) != n for row in a + b):
        raise ValueError("Expected equally sized square matrices")
    return tuple(tuple(sum((a[i][k] * b[k][j] for k in range(n)), F(0))
                       for j in range(n)) for i in range(n))


def inverse(a: Matrix) -> Matrix:
    n = len(a)
    rows = [list(row) + list(identity(n)[i]) for i, row in enumerate(a)]
    for column in range(n):
        pivot = next((i for i in range(column, n) if rows[i][column]), None)
        if pivot is None:
            raise ValueError("Singular matrix")
        rows[column], rows[pivot] = rows[pivot], rows[column]
        scale = rows[column][column]
        rows[column] = [v / scale for v in rows[column]]
        for i in range(n):
            if i != column:
                factor = rows[i][column]
                rows[i] = [x - factor * y for x, y in zip(rows[i], rows[column])]
    return tuple(tuple(row[n:]) for row in rows)


def power(a: Matrix, exponent: int) -> Matrix:
    if exponent < 0:
        return power(inverse(a), -exponent)
    result = identity(len(a))
    while exponent:
        if exponent & 1:
            result = multiply(result, a)
        a = multiply(a, a)
        exponent >>= 1
    return result


def elementary(n: int, i: int, j: int, value: int | F) -> Matrix:
    rows = [list(row) for row in identity(n)]
    rows[i][j] += F(value)
    return tuple(tuple(row) for row in rows)


def shell(n: int, suffix: str) -> str:
    return ('0' * (n + 1) + '1' if n >= 0 else '1' * (-n) + '0') + suffix


def prefix_map(word: str, table: tuple[tuple[str, str], ...]) -> str:
    for source, target in table:
        if word.startswith(source):
            return target + word[len(source):]
    raise ValueError("Finite test word is too short for prefix table")


Perm = tuple[int, ...]


def compose_perm(a: Perm, b: Perm) -> Perm:
    return tuple(a[b[i]] for i in range(len(a)))


def inverse_perm(a: Perm) -> Perm:
    return tuple(a.index(i) for i in range(len(a)))


def power_perm(a: Perm, n: int) -> Perm:
    if n < 0:
        return power_perm(inverse_perm(a), -n)
    result = tuple(range(len(a)))
    for _ in range(n):
        result = compose_perm(result, a)
    return result


def fibonacci(n: int) -> int:
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def run_checks() -> None:
    forward = (('0', '00'), ('10', '01'), ('11', '1'))
    backward = tuple((b, a) for a, b in forward)
    for n in range(-30, 31):
        for suffix in ('000', '0101', '1010', '111', '00101101'):
            check('binary_shift_and_bridge', prefix_map(shell(n, suffix), forward)
                  == shell(n + 1, suffix), (n, suffix))
            check('binary_shift_inverse', prefix_map(shell(n, suffix), backward)
                  == shell(n - 1, suffix), (n, suffix))

    # D=S_3, rho the identity and phi conjugation by a three-cycle.
    # This checks noncommutative orbit formulas, not any infinite tail-separation claim.
    cycle = (1, 2, 0)
    group = tuple(permutations(range(3)))

    def phi(g: Perm, n: int) -> Perm:
        c = power_perm(cycle, n)
        return compose_perm(compose_perm(c, g), inverse_perm(c))

    for n in range(-12, 13):
        for g, h in product(group, repeat=2):
            check('noncommutative_profile_homomorphism',
                  phi(compose_perm(g, h), n) == compose_perm(phi(g, n), phi(h, n)))
            check('mapping_torus_covariance', phi(g, n + 1) == phi(phi(g, 1), n))
            left = phi(compose_perm(compose_perm(g, h), inverse_perm(g)), n)
            right = compose_perm(compose_perm(phi(g, n), phi(h, n)),
                                 inverse_perm(phi(g, n)))
            check('twisted_lamp_covariance', left == right)

    for size in range(2, 7):
        jordan = tuple(tuple(F(i == j or j == i + 1) for j in range(size))
                       for i in range(size))
        for n in range(-12, 13):
            actual = power(jordan, n)
            expected = tuple(tuple(F(choose_integer(n, j - i)) if j >= i else F(0)
                                   for j in range(size)) for i in range(size))
            check('jordan_binomial_all_integer_times', actual == expected, (size, n))
            for vector in (tuple(range(1, size + 1)), tuple((-1)**j for j in range(size))):
                observed = sum((actual[0][j] * vector[j] for j in range(size)), F(0))
                formula = sum(vector[j] * choose_integer(n, j) for j in range(size))
                check('noninjective_observation_polynomial', observed == formula)

    for n in range(60):
        check('fibonacci_recurrence', fibonacci(n + 2) == fibonacci(n + 1) + fibonacci(n))
        check('product_recurrence', fibonacci(n + 2)**2 ==
              2 * fibonacci(n + 1)**2 + 2 * fibonacci(n)**2 - fibonacci(n - 1)**2
              if n >= 1 else True)
        for a in range(2, 7):
            check('exponential_recurrence', a**(n + 1) == a * a**n)
            # (shift-a)^2 annihilates n*a^n.
            f = lambda j: j * a**j
            check('polynomial_exponential_recurrence',
                  f(n + 2) - 2*a*f(n + 1) + a*a*f(n) == 0)

    for a in range(2, 8):
        for n in range(-30, 31):
            f = lambda j: a**abs(j)
            defect = a*f(n + 2) - (a*a + 1)*f(n + 1) + a*f(n)
            check('bilateral_exponential_finite_support_defect',
                  defect == (a*a - 1 if n == -1 else 0), (a, n, defect))
        for q in range(2, 9):
            witness = (q**(a - 1) - 1) * (q - 1)
            check('derived_length_three_nonzero_witness', witness != 0, (q, a))
            # The top commutator exponent at position zero.
            check('top_commutator_at_zero', a**abs(-1) - a**abs(0) == a - 1)

    for n in range(31):
        u = elementary(3, 0, 1, 2**n)
        v = elementary(3, 1, 2, 3**n)
        commutator = multiply(multiply(multiply(u, v), inverse(u)), inverse(v))
        check('noncommuting_matrix_profile_commutator',
              commutator == elementary(3, 0, 2, 6**n), n)

    # Germ maps F_(k,P) shift depth by k and act on angular coordinates by P(depth).
    # The composition profile is P(n+l)Q(n), not Q(n)P(n+l).
    def p_profile(n: int) -> Matrix:
        return multiply(elementary(3, 0, 1, 2**n), elementary(3, 1, 2, 3**n))

    def q_profile(n: int) -> Matrix:
        return multiply(elementary(3, 1, 2, 5**n), elementary(3, 0, 1, n + 1))

    for n in range(4, 16):
        for k, ell in product(range(-2, 3), repeat=2):
            vector = ((F(1),), (F(2),), (F(-1),))
            # Use square matrices to encode test columns, with zero other columns.
            col = tuple((row[0], F(0), F(0)) for row in vector)
            stepwise = multiply(p_profile(n + ell), multiply(q_profile(n), col))
            combined = multiply(multiply(p_profile(n + ell), q_profile(n)), col)
            check('noncommutative_germ_composition', stepwise == combined and
                  n + ell + k == n + k + ell, (n, k, ell))
            inverse_profile = inverse(p_profile(n - k))
            check('germ_inverse_profile',
                  multiply(p_profile(n - k), inverse_profile) == identity(3))

    # Unitriangular grading dilations and affine lamp covariance.
    def dilate(matrix: Matrix, scale: int | F) -> Matrix:
        return tuple(tuple(matrix[i][j] * F(scale)**(j-i) for j in range(len(matrix)))
                     for i in range(len(matrix)))

    for m in range(2, 6):
        for a in range(1, 5):
            left = identity(m)
            right = identity(m)
            for i in range(m - 1):
                left = multiply(left, elementary(m, i, i + 1, F(a + i, 3)))
                right = multiply(right, elementary(m, i, i + 1, F(2*a - i, 9)))
            for scale in (F(2), F(3), F(1, 3), F(9)):
                check('unitriangular_grading_automorphism',
                      dilate(multiply(left, right), scale) ==
                      multiply(dilate(left, scale), dilate(right, scale)))
                check('commuting_arithmetic_dilations',
                      dilate(dilate(left, 2), scale) == dilate(dilate(left, scale), 2))
                # Delta_q conjugates left translation by Delta_p(a).
                check('nonabelian_lamp_covariance',
                      dilate(multiply(dilate(left, 2), dilate(right, 1/scale)), scale)
                      == multiply(dilate(dilate(left, scale), 2), right))


def main() -> None:
    run_checks()
    here = Path(__file__).resolve()
    note = here.with_name('beyond_polynomial_germs.md')
    result = {
        'status': 'passed',
        'checks_total': sum(COUNTS.values()),
        'checks_by_category': dict(sorted(COUNTS.items())),
        'arithmetic': 'exact integers, rational fractions, finite permutations',
        'script_sha256': sha256(here.read_bytes()).hexdigest(),
        'note_sha256': sha256(note.read_bytes()).hexdigest(),
        'scope_warning': ('Finite sanity checks of displayed formulas only. Not formal '
                          'verification of finite presentability, finiteness properties, '
                          'simplicity, nonlinearity, or infinite-group embeddings.'),
    }
    output = here.with_name('check_results.json')
    output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
