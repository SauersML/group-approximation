"""Exact all-position search for two depth-one Leavitt root excursions.

The coefficient normal form is the faithful binary-prefix replacement form:
the pair (mu, nu) denotes s_mu t_nu and is expanded by
(mu,nu)=(mu0,nu0)+(mu1,nu1).  Run on MSI, never locally.
"""

from collections import deque
from itertools import product


COORDS = (2, 4, 5, 6, 7, 8, 9)
INDEX = {coordinate: index for index, coordinate in enumerate(COORDS)}
ARROWS = (
    (6, 5), (5, 4), (4, 2), (8, 2), (9, 4),
    (9, 2), (9, 7), (5, 7), (6, 7), (6, 8),
)
WORDS = ("", "0", "1")
COEFFICIENTS = tuple((mu, nu) for mu in WORDS for nu in WORDS if (mu, nu) != ("", ""))
COEFFICIENT_NAMES = {
    ("0", ""): "s0", ("1", ""): "s1",
    ("", "0"): "t0", ("", "1"): "t1",
    ("0", "0"): "s0t0", ("0", "1"): "s0t1",
    ("1", "0"): "s1t0", ("1", "1"): "s1t1",
}
ZERO = frozenset()
ONE = frozenset((("", ""),))


def binary_words(length):
    return ("",) if length == 0 else tuple("".join(bits) for bits in product("01", repeat=length))


def canonical(terms):
    terms = tuple(terms)
    if not terms:
        return ZERO
    depth = max(len(nu) for _, nu in terms)
    answer = set()
    for mu, nu in terms:
        for suffix in binary_words(depth - len(nu)):
            term = (mu + suffix, nu + suffix)
            if term in answer:
                answer.remove(term)
            else:
                answer.add(term)
    return frozenset(answer)


def add(left, right):
    return canonical(tuple(left) + tuple(right))


def multiply_monomials(left, right):
    mu, nu = left
    alpha, beta = right
    if alpha.startswith(nu):
        return (mu + alpha[len(nu):], beta)
    if nu.startswith(alpha):
        return (mu, beta + nu[len(alpha):])
    return None


def multiply(left, right):
    terms = []
    for first in left:
        for second in right:
            term = multiply_monomials(first, second)
            if term is not None:
                terms.append(term)
    return canonical(terms)


def equal(left, right):
    depth = max(
        (len(nu) for _, nu in tuple(left) + tuple(right)),
        default=0,
    )
    return canonical(
        tuple((mu + suffix, nu + suffix) for mu, nu in left
              for suffix in binary_words(depth - len(nu)))
    ) == canonical(
        tuple((mu + suffix, nu + suffix) for mu, nu in right
              for suffix in binary_words(depth - len(nu)))
    )


def constant_bit(element):
    if not element:
        return 0
    if equal(element, ONE):
        return 1
    return None


def zero_matrix():
    return [[ZERO for _ in COORDS] for _ in COORDS]


def identity_matrix():
    matrix = zero_matrix()
    for index in range(7):
        matrix[index][index] = ONE
    return matrix


def constant_transvection(source, target):
    matrix = identity_matrix()
    matrix[INDEX[target]][INDEX[source]] = ONE
    return matrix


def left_elementary(matrix, source, target, coefficient):
    source_row = INDEX[source]
    target_row = INDEX[target]
    result = [row[:] for row in matrix]
    for column in range(7):
        result[target_row][column] = add(
            result[target_row][column],
            multiply(coefficient, matrix[source_row][column]),
        )
    return result


def right_elementary(matrix, source, target, coefficient):
    source_column = INDEX[source]
    target_column = INDEX[target]
    result = [row[:] for row in matrix]
    for row in range(7):
        result[row][source_column] = add(
            result[row][source_column],
            multiply(matrix[row][target_column], coefficient),
        )
    return result


def conjugate_generator(first, second, generator):
    # If g=x(first)x(second), then g^-1 h g=x(second)x(first)h x(first)x(second).
    source1, target1, coefficient1 = first
    source2, target2, coefficient2 = second
    matrix = constant_transvection(*generator)
    matrix = left_elementary(matrix, source1, target1, coefficient1)
    matrix = left_elementary(matrix, source2, target2, coefficient2)
    matrix = right_elementary(matrix, source1, target1, coefficient1)
    matrix = right_elementary(matrix, source2, target2, coefficient2)
    return matrix


def to_constant_matrix(matrix):
    rows = []
    for row in matrix:
        bits = 0
        for column, entry in enumerate(row):
            bit = constant_bit(entry)
            if bit is None:
                return None
            bits |= bit << column
        rows.append(bits)
    return tuple(rows)


def binary_multiply(left, right):
    product_rows = []
    for left_row in left:
        row = 0
        for index in range(7):
            if (left_row >> index) & 1:
                row ^= right[index]
        product_rows.append(row)
    return tuple(product_rows)


def signed_l0():
    identity = tuple(1 << index for index in range(7))
    generators = []
    for source, target in ARROWS:
        rows = list(identity)
        rows[INDEX[target]] ^= 1 << INDEX[source]
        generators.append(tuple(rows))
    character = {identity: 0}
    queue = deque((identity,))
    while queue:
        current = queue.popleft()
        for index, generator in enumerate(generators):
            successor = binary_multiply(current, generator)
            sign = character[current] ^ (index < 3)
            if successor in character:
                assert character[successor] == sign
            else:
                character[successor] = sign
                queue.append(successor)
    assert len(character) == 8192
    return character


def root_normalizes(root, character):
    dummy = (root[0], root[1], root[2])
    identity_root = (root[0], root[1], ZERO)
    return pair_normalizes(dummy, identity_root, character)


def pair_normalizes(first, second, character):
    for generator_index, generator in enumerate(ARROWS):
        conjugate = conjugate_generator(first, second, generator)
        constant = to_constant_matrix(conjugate)
        if constant is None:
            return False
        if constant not in character or character[constant] != (generator_index < 3):
            return False
    return True


def pair_product_is_constant(first, second):
    # Apply the two elementary matrices to the identity and inspect entries.
    source1, target1, coefficient1 = first
    source2, target2, coefficient2 = second
    matrix = identity_matrix()
    matrix = left_elementary(matrix, source2, target2, coefficient2)
    matrix = left_elementary(matrix, source1, target1, coefficient1)
    return to_constant_matrix(matrix) is not None


def format_root(root):
    source, target, coefficient = root
    monomial = next(iter(coefficient))
    return f"x_{target}{source}({COEFFICIENT_NAMES[monomial]})"


def main():
    # Sanity checks for the prefix normal form and multiplication orientation.
    monomial = lambda pair: canonical((pair,))
    s0, s1 = monomial(("0", "")), monomial(("1", ""))
    t0, t1 = monomial(("", "0")), monomial(("", "1"))
    assert equal(multiply(t0, s0), ONE)
    assert equal(multiply(t1, s1), ONE)
    assert not multiply(t0, s1)
    assert not multiply(t1, s0)
    assert equal(add(multiply(s0, t0), multiply(s1, t1)), ONE)

    character = signed_l0()
    positions = tuple((source, target) for source in COORDS for target in COORDS if source != target)
    roots = tuple(
        (source, target, canonical((coefficient,)))
        for source, target in positions
        for coefficient in COEFFICIENTS
    )
    individually_outside = tuple(root for root in roots if not root_normalizes(root, character))
    individually_inside = tuple(root for root in roots if root not in individually_outside)
    inside_positions = {(root[0], root[1]) for root in individually_inside}
    assert inside_positions == {(6, 2), (6, 7), (9, 2), (9, 7)}
    assert len(individually_outside) == 304
    assert len(individually_inside) == 32
    print("depth-one nonconstant roots", len(roots))
    print("individually outside signed normalizer", len(individually_outside))
    print("individual nonconstant normalizers", len(individually_inside))
    print("individual normalizer positions", sorted(inside_positions))

    paired_hits = []
    constant_hits = 0
    same_root_hits = 0
    tested = 0
    for first in individually_outside:
        for second in individually_outside:
            tested += 1
            if not pair_normalizes(first, second, character):
                continue
            if pair_product_is_constant(first, second):
                constant_hits += 1
                if first[:2] == second[:2]:
                    same_root_hits += 1
                continue
            paired_hits.append((first, second))
            if len(paired_hits) <= 20:
                print("genuine hit", format_root(first), format_root(second))

    print("ordered pairs tested", tested)
    print("constant normalizing products", constant_hits)
    print("same-root constant products", same_root_hits)
    print("genuine paired returns", len(paired_hits))
    assert tested == 304 * 304
    assert constant_hits == same_root_hits == 338
    assert not paired_hits


if __name__ == "__main__":
    main()
