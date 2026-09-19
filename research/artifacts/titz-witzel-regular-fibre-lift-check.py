#!/usr/bin/env python3
"""Exhaust regular nonabelian fibre lifts of the two-generator Titz gate.

The carrier is F x C2.  After gauge normalization,

    e(x, 0) = (x, 1),       e(x, 1) = (x, 0),
    u(x, 0) = (a*x, 1),     u(x, 1) = (b*x, 0).

Here F acts on itself regularly on the left.  An even word preserves each
block and acts there by a deck transformation, so its normalized Hamming
defect is half the number of nonidentity block holonomies.  This script
derives those holonomy words symbolically and exhausts a,b in the requested
small fibres.  The general obstruction is a proof independent of this finite
enumeration; see the accompanying report.
"""

from itertools import permutations


def reduce_word(word):
    out = []
    for letter in word:
        if out and out[-1] == -letter:
            out.pop()
        else:
            out.append(letter)
    return tuple(out)


def product_word(*words):
    return reduce_word(tuple(letter for word in words for letter in word))


def inverse_word(word):
    return tuple(-letter for letter in reversed(word))


def power_word(word, exponent):
    if exponent < 0:
        return power_word(inverse_word(word), -exponent)
    return product_word(*(word for _ in range(exponent)))


def gate_words():
    # Generator 1 is e and generator 2 is u.  Only e is reduced as an
    # involution in the presentation words.
    def reduce_gate(word):
        out = []
        for letter in word:
            if abs(letter) == 1:
                letter = 1
            if out and (out[-1] == -letter or (letter == 1 and out[-1] == 1)):
                out.pop()
            else:
                out.append(letter)
        return tuple(out)

    def p(*words):
        return reduce_gate(tuple(letter for word in words for letter in word))

    def inv(word):
        return tuple(-letter for letter in reversed(word))

    def pw(word, exponent):
        if exponent < 0:
            return pw(inv(word), -exponent)
        return p(*(word for _ in range(exponent)))

    e, u = (1,), (2,)
    h = p(u, e, inv(u))
    a = p(e, h, e)
    x = p(a, pw(u, 2))
    c = p(pw(u, 2), a, pw(u, 2))
    f = p(inv(x), h, x)
    d = p(e, inv(a), f)
    s = p(f, a, f)
    rho = p(inv(x), inv(s), inv(c))
    beta = p(rho, e, inv(rho))
    sandwich = p(beta, a)
    return {
        "c2": pw(c, 2),
        "rho": p(pw(rho, 2), e, inv(u)),
        "P": p(sandwich, u, inv(d)),
        "J": p(sandwich, u, sandwich, c),
        "mark": pw(u, 8),
    }


# A lift is represented by its two fibre words and its permutation of blocks.
# A fibre word is in letters 1=a, 2=b.
IDENTITY_LIFT = (((), ()), (0, 1))
E_LIFT = (((), ()), (1, 0))
U_LIFT = (((1,), (2,)), (1, 0))


def compose_lifts(left, right):
    left_words, left_blocks = left
    right_words, right_blocks = right
    return (
        tuple(
            product_word(left_words[right_blocks[block]], right_words[block])
            for block in (0, 1)
        ),
        tuple(left_blocks[right_blocks[block]] for block in (0, 1)),
    )


def inverse_lift(lift):
    words, blocks = lift
    inverse_blocks = (blocks.index(0), blocks.index(1))
    inverse_words = [None, None]
    for block in (0, 1):
        inverse_words[blocks[block]] = inverse_word(words[block])
    return tuple(inverse_words), inverse_blocks


def holonomy_words(word):
    result = IDENTITY_LIFT
    for letter in word:
        image = E_LIFT if abs(letter) == 1 else U_LIFT
        if letter < 0:
            image = inverse_lift(image)
        result = compose_lifts(result, image)
    words, blocks = result
    assert blocks == (0, 1), "all retained relators and the mark have even parity"
    return words


def permutation_product(left, right):
    return tuple(left[right[index]] for index in range(len(left)))


def permutation_inverse(permutation):
    out = [0] * len(permutation)
    for index, image in enumerate(permutation):
        out[image] = index
    return tuple(out)


def permutation_groups():
    s3 = list(permutations(range(3)))
    a4 = [
        permutation
        for permutation in permutations(range(4))
        if sum(
            permutation[i] > permutation[j]
            for i in range(4)
            for j in range(i + 1, 4)
        )
        % 2
        == 0
    ]
    return (
        ("S3", s3, permutation_product, permutation_inverse, tuple(range(3))),
        ("A4", a4, permutation_product, permutation_inverse, tuple(range(4))),
    )


def d8_group():
    elements = [(rotation, reflection) for rotation in range(4) for reflection in range(2)]

    def multiply(left, right):
        sign = -1 if left[1] else 1
        return ((left[0] + sign * right[0]) % 4, (left[1] + right[1]) % 2)

    def invert(element):
        sign = -1 if element[1] else 1
        return ((-sign * element[0]) % 4, element[1])

    return "D8", elements, multiply, invert, (0, 0)


def q8_group():
    # (sign,basis), with basis 0=1, 1=i, 2=j, 3=k.
    elements = [(sign, basis) for sign in (1, -1) for basis in range(4)]
    positive_table = (
        ((1, 0), (1, 1), (1, 2), (1, 3)),
        ((1, 1), (-1, 0), (1, 3), (-1, 2)),
        ((1, 2), (-1, 3), (-1, 0), (1, 1)),
        ((1, 3), (1, 2), (-1, 1), (-1, 0)),
    )

    def multiply(left, right):
        sign, basis = positive_table[left[1]][right[1]]
        return left[0] * right[0] * sign, basis

    def invert(element):
        return element if element[1] == 0 else (-element[0], element[1])

    return "Q8", elements, multiply, invert, (1, 0)


def heisenberg_group(prime):
    elements = [
        (a, b, c)
        for a in range(prime)
        for b in range(prime)
        for c in range(prime)
    ]

    def multiply(left, right):
        return (
            (left[0] + right[0]) % prime,
            (left[1] + right[1]) % prime,
            (left[2] + right[2] + left[0] * right[1]) % prime,
        )

    def invert(element):
        return (
            -element[0] % prime,
            -element[1] % prime,
            (-element[2] + element[0] * element[1]) % prime,
        )

    return f"H{prime}", elements, multiply, invert, (0, 0, 0)


def evaluate_fibre_word(word, a, b, multiply, invert, identity):
    result = identity
    for letter in word:
        image = a if abs(letter) == 1 else b
        result = multiply(result, invert(image) if letter < 0 else image)
    return result


def scan(group, holonomies):
    name, elements, multiply, invert, identity = group
    distribution = {}
    exact = 0
    marked = 0
    best = None
    for a in elements:
        for b in elements:
            defects = tuple(
                sum(
                    evaluate_fibre_word(
                        word, a, b, multiply, invert, identity
                    )
                    != identity
                    for word in holonomies[relator]
                )
                for relator in ("c2", "rho", "P", "J")
            )
            mark = sum(
                evaluate_fibre_word(word, a, b, multiply, invert, identity)
                != identity
                for word in holonomies["mark"]
            )
            distribution[(defects, mark)] = distribution.get((defects, mark), 0) + 1
            exact += not any(defects)
            marked += mark != 0
            if mark:
                key = (sum(defects) / mark, max(defects) / mark, defects)
                if best is None or key < best[0]:
                    best = key, a, b, mark

    # No exact packet may separate the finite-residual mark.
    assert all(mark == 0 for (defects, mark) in distribution if not any(defects))
    print(
        f"{name}: order={len(elements)} pairs={len(elements) ** 2} "
        f"marked={marked} exact={exact} best={best}"
    )
    print(f"  distribution={distribution}")


def main():
    holonomies = {
        name: holonomy_words(word) for name, word in gate_words().items()
    }
    # The two block holonomies of u^8 are (ba)^4 and (ab)^4, hence are
    # conjugate.  A regular packet's mark is therefore either zero or full.
    assert holonomies["mark"] == (
        (2, 1, 2, 1, 2, 1, 2, 1),
        (1, 2, 1, 2, 1, 2, 1, 2),
    )
    groups = (
        *permutation_groups(),
        d8_group(),
        q8_group(),
        heisenberg_group(3),
        heisenberg_group(5),
        heisenberg_group(7),
    )
    for group in groups:
        scan(group, holonomies)


if __name__ == "__main__":
    main()
