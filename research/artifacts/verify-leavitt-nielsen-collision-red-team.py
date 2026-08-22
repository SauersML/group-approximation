#!/usr/bin/env python3
"""Exact symbolic audit of the first hidden Nielsen-collision relation.

The standard module basis is ``(matrix coordinate, infinite binary word)``.
For an identity containing at most ``d`` deletion operators, it is enough to
split the word into its ``2^d`` possible initial cylinders.  The unexamined
tail remains an opaque common symbol, so this is an exact symbolic check, not
a finite truncation of the Leavitt algebra.
"""

from itertools import product

N = 20


def ring_action(coefficient, prefix):
    """Apply a Leavitt monomial to ``prefix + opaque_tail``."""
    for kind, bit in reversed(coefficient):
        if kind == "s":
            prefix = bit + prefix
        else:
            if not prefix:
                raise AssertionError("cylinder depth was not sufficient")
            if prefix[0] != bit:
                return None
            prefix = prefix[1:]
    return prefix


def toggle(vector, term):
    if term in vector:
        vector.remove(term)
    else:
        vector.add(term)


def act(factor, vector):
    if factor[0] == "p":
        return {((coordinate + factor[1]) % N, prefix)
                for coordinate, prefix in vector}

    _, coefficient, row, column = factor
    result = set(vector)
    for coordinate, prefix in vector:
        if coordinate != column:
            continue
        image = ring_action(coefficient, prefix)
        if image is not None:
            toggle(result, (row, image))
    return result


def evaluate(word, vector):
    # A left-to-right group word acts on a column vector right-to-left.
    for factor in reversed(word):
        vector = act(factor, vector)
    return vector


def inverse(word):
    result = []
    for factor in reversed(word):
        if factor[0] == "p":
            result.append(("p", -factor[1]))
        else:
            # Every root used below is square-zero, hence its characteristic
            # two elementary transvection is an involution.
            result.append(factor)
    return tuple(result)


def assert_same_action(left, right):
    deletion_depth = max(
        sum(sum(kind == "t" for kind, _ in factor[1])
            for factor in word if factor[0] == "r")
        for word in (left, right)
    )
    for bits in product("01", repeat=deletion_depth):
        prefix = "".join(bits)
        for coordinate in range(N):
            vector = {(coordinate, prefix)}
            assert evaluate(left, vector) == evaluate(right, vector)


S0 = (("s", "0"),)
S1 = (("s", "1"),)
T0 = (("t", "0"),)
T1 = (("t", "1"),)
S0S1 = S0 + S1


def root(row, column, coefficient):
    return ("r", coefficient, row, column)


A = (root(0, 1, S0),)
E = (root(0, 1, T1),)
Q = (root(2, 3, S1), root(10, 11, T0))
P = (("p", 1),)
R = Q + P

# Literal Leavitt-unit identities used in the paper proof.
assert_same_action(A + A, ())
assert_same_action(E + E, ())
assert_same_action(Q + Q, ())

RAR = R + A + inverse(R)
RAR_EXPECTED = (root(1, 2, S0), root(1, 3, S0S1))
assert_same_action(RAR, RAR_EXPECTED)

R2AR2 = R + R + A + inverse(R) + inverse(R)
R2AR2_EXPECTED = (root(2, 3, S0), root(2, 4, S0S1))
assert_same_action(R2AR2, R2AR2_EXPECTED)

# The two displayed roots have disjoint row/column incidences with x_12(s0).
V = R2AR2_EXPECTED
OMEGA = A + V + A + inverse(V)
assert_same_action(OMEGA, ())


def free_product_reduce(word):
    """Normal form in (<x> * C2(y) * C2(u)) * <s>."""
    output = []

    def reduce_base(base):
        reduced = []
        for letter, exponent in base:
            if letter in {"y", "u"}:
                exponent %= 2
            if not exponent:
                continue
            if reduced and reduced[-1][0] == letter:
                exponent += reduced.pop()[1]
                if letter in {"y", "u"}:
                    exponent %= 2
                if exponent:
                    reduced.append((letter, exponent))
            else:
                reduced.append((letter, exponent))
        return tuple(reduced)

    for factor, value in word:
        if factor == "A":
            value = reduce_base(value)
            if not value:
                continue
        if output and output[-1][0] == factor:
            old = output.pop()[1]
            value = old + value if factor == "s" else reduce_base(old + value)
            if value:
                output.append((factor, value))
        else:
            output.append((factor, value))
    return tuple(output)


def formal_inverse(word):
    result = []
    for factor, value in reversed(word):
        if factor == "s":
            result.append(("s", -value))
        else:
            result.append((
                "A", tuple((letter, -exponent)
                           for letter, exponent in reversed(value))))
    return free_product_reduce(result)


def formal_product(*words):
    result = ()
    for word in words:
        result = free_product_reduce(result + word)
    return result


def formal_power(word, exponent):
    factor = word if exponent >= 0 else formal_inverse(word)
    result = ()
    for _ in range(abs(exponent)):
        result = formal_product(result, factor)
    return result


def base(letter, exponent=1):
    return (("A", ((letter, exponent),)),)


X = base("x")
Y = base("y")
U = base("u")
S = (("s", 1),)

# Tietze elimination of
#   x z h z y z^-1,  u z u z k z^-1,  with s=z^-1.
H_IMAGE = formal_product(S, formal_inverse(X), formal_inverse(S),
                         formal_inverse(Y), S)
K_IMAGE = formal_product(S, U, S, U, formal_inverse(S))

z = formal_inverse(S)
assert not formal_product(X, z, H_IMAGE, z, Y, S)
assert not formal_product(U, z, U, z, K_IMAGE, S)

# In the actual first corner group b=h0*h1=(qp)_1.  Its Tietze image is
# B=x*h.  The hidden coefficient identity Omega=[u,b^2 u b^-2] is not a
# coefficient-boundary word after substitution: its reduced normal form still
# has 24 nonzero s-syllables (49 alternating free-product syllables total).
B_IMAGE = formal_product(X, H_IMAGE)
CONJUGATE = formal_product(formal_power(B_IMAGE, 2), U,
                           formal_power(B_IMAGE, -2))
OMEGA_IMAGE = formal_product(U, CONJUGATE, U,
                             formal_inverse(CONJUGATE))
assert OMEGA_IMAGE
assert len(OMEGA_IMAGE) == 49
assert sum(factor == "s" for factor, _ in OMEGA_IMAGE) == 24


def exponent_after_killing(word, survivor):
    exponent = 0
    for factor, value in word:
        if factor != "A":
            continue
        exponent += sum(power for letter, power in value if letter == survivor)
    return exponent % 2 if survivor in {"y", "u"} else exponent


# The one-relator quotient by this hidden face still maps onto each visible
# base factor separately.  In particular the face alone cannot kill x, y, or
# u; these are honest quotient maps, not finite-model tests.
assert exponent_after_killing(OMEGA_IMAGE, "x") == 0
assert exponent_after_killing(OMEGA_IMAGE, "y") == 0
assert exponent_after_killing(OMEGA_IMAGE, "u") == 0

print("PASS: exact cylinder-module audit proves the two conjugation formulas")
print("PASS: [a,(qp)^2 a (qp)^-2]=1 in the Leavitt unit group")
print("PASS: both Tietze substitutions satisfy their formal relators")
print("PASS: the hidden relation has a nonempty 49-syllable Tietze image")
print("PASS: killing that image alone retains the x, y, and u quotients")
