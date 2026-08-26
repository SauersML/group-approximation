"""Audit short odd mixed words around the endpoint fine collision.

Run only through MSI.  The endpoint Whitehead is W=What_(8,2;2), the
literal row-two arm is A2=x_58(a2), and M=J2 B3 A2 is the native
order-seven head.  We search for the shortest odd-W words which return the
signed fine Hecke group K2, and print the exact actions of the primitive
mixed words on the two fine generators s and s'=WsW.
"""

from collections import deque

from depth_one_paired_leavitt_return_search import binary_words
from endpoint_chain_center_hecke_collision_audit import (
    coeff, conjugate, entries, fixed_key, right_depth, root, whitehead,
)
from signed_hecke_literal_pauli_probe_audit import (
    COORDS, identity_matrix, matrix_multiply, word_matrix,
)


def multiply(*matrices):
    answer = identity_matrix()
    for matrix in matrices:
        answer = matrix_multiply(answer, matrix)
    return answer


def power(matrix, exponent):
    answer = identity_matrix()
    for _ in range(exponent):
        answer = matrix_multiply(answer, matrix)
    return answer


def inverse(matrix, order):
    return power(matrix, order - 1)


def conjugate_matrix(actor, actor_inverse, matrix):
    return multiply(actor, matrix, actor_inverse)


PREFIXES = tuple(binary_words(3))
PREFIX_INDEX = {word: index for index, word in enumerate(PREFIXES)}
BIT_DIMENSION = len(COORDS) * len(PREFIXES)
BIT_IDENTITY = tuple(1 << index for index in range(BIT_DIMENSION))


def to_bits(matrix):
    """Faithful action on the complete depth-three prefix module."""
    key = fixed_key(matrix, 3)
    columns = [0] * BIT_DIMENSION
    for row_index, row in enumerate(key):
        for column_index, entry in enumerate(row):
            for mu, nu in entry:
                source = column_index * len(PREFIXES) + PREFIX_INDEX[nu]
                target = row_index * len(PREFIXES) + PREFIX_INDEX[mu]
                columns[source] ^= 1 << target
    return tuple(columns)


def bit_apply(matrix, vector):
    answer = 0
    while vector:
        lowest = vector & -vector
        answer ^= matrix[lowest.bit_length() - 1]
        vector ^= lowest
    return answer


def bit_multiply(left, right):
    return tuple(bit_apply(left, column) for column in right)


def bit_power(matrix, exponent):
    answer = BIT_IDENTITY
    for _ in range(exponent):
        answer = bit_multiply(answer, matrix)
    return answer


def bit_order(matrix, bound=10000):
    current = BIT_IDENTITY
    for exponent in range(1, bound + 1):
        current = bit_multiply(current, matrix)
        if current == BIT_IDENTITY:
            return exponent
    return None


def bit_generated_signed(generators):
    seen = {BIT_IDENTITY: 0}
    frontier = [BIT_IDENTITY]
    while frontier:
        current = frontier.pop()
        sign = seen[current]
        for generator, generator_sign in generators:
            nxt = bit_multiply(current, generator)
            nxt_sign = sign ^ generator_sign
            if nxt in seen:
                assert seen[nxt] == nxt_sign
            else:
                seen[nxt] = nxt_sign
                frontier.append(nxt)
    return seen


def main():
    q = coeff("1", "1")
    a1 = coeff("1", "0")
    a2 = coeff("1", "00")
    b3 = coeff("000", "1")

    named = {
        "C1": root(4, 2, q),
        "C2": root(5, 4, q),
        "C3": root(6, 5, q),
        "v": root(5, 7, a1),
        "w": root(6, 7, a1),
        "s": root(6, 8, a2),
        "A2": root(5, 8, a2),
        "B3": root(9, 5, b3),
    }
    w_word = whitehead(8, 2, 2)
    j2_word = whitehead(9, 8, 2)
    named["W"] = word_matrix(w_word)
    named["J2"] = word_matrix(j2_word)
    named["M"] = multiply(named["J2"], named["B3"], named["A2"])
    named["sprime"] = conjugate(w_word, named["s"])
    named["A2prime"] = conjugate(w_word, named["A2"])

    k1_names = ("C1", "C2", "C3", "v", "w")
    k2_names = k1_names + ("s",)
    named_bits = {name: to_bits(matrix) for name, matrix in named.items()}
    k1 = bit_generated_signed(tuple(
        (named_bits[name], name.startswith("C")) for name in k1_names
    ))
    k2 = bit_generated_signed(tuple(
        (named_bits[name], name.startswith("C")) for name in k2_names
    ))

    print("primitive orders")
    for name in ("W", "A2", "B3", "J2", "M"):
        print(name, bit_order(named_bits[name]), flush=True)

    print("primitive conjugates of fine roots")
    actor_orders = {"W": 2, "A2": 2, "B3": 2, "J2": 2, "M": 7}
    for actor_name in actor_orders:
        actor = named_bits[actor_name]
        actor_inverse = bit_power(actor, actor_orders[actor_name] - 1)
        print(actor_name)
        for fine_name in ("s", "sprime", "A2", "A2prime"):
            image = bit_multiply(bit_multiply(actor, named_bits[fine_name]),
                                 actor_inverse)
            matches = tuple(name for name, value in named_bits.items()
                            if value == image)
            print(" ", fine_name, "matches", matches,
                  "inK1", image in k1, "inK2", image in k2)

    primitive_words = {
        "W*A2": ("W", "A2"),
        "A2*W": ("A2", "W"),
        "[W,A2]": ("W", "A2", "W", "A2"),
        "W*M": ("W", "M"),
        "M*W": ("M", "W"),
        "[W,M]": ("W", "M", "W", "Minv"),
        "[M,W]": ("M", "W", "Minv", "W"),
    }
    atoms = dict(named_bits)
    atoms["Minv"] = bit_power(named_bits["M"], 6)

    print("short mixed words")
    for label, letters in primitive_words.items():
        matrix = BIT_IDENTITY
        for letter in letters:
            matrix = bit_multiply(matrix, atoms[letter])
        order = bit_order(matrix)
        inverse_matrix = bit_power(matrix, order - 1)
        print(label, "letters", letters, "order", order,
              flush=True)
        for fine_name in ("s", "sprime"):
            image = bit_multiply(bit_multiply(matrix, named_bits[fine_name]),
                                 inverse_matrix)
            matches = tuple(name for name, value in named_bits.items()
                            if value == image)
            print(" ", fine_name, "matches", matches,
                  "inK1", image in k1, "inK2", image in k2)

    # Breadth-first screen in <W,A2,M>.  The state remembers literal W parity,
    # so a matrix reached with both parities is retained twice.  A signed K2
    # return means conjugation preserves the prescribed character on all six
    # generators, not merely that the abstract subgroup has the same order.
    generators = {
        "W": (named_bits["W"], named_bits["W"], 1),
        "A": (named_bits["A2"], named_bits["A2"], 0),
        "M": (named_bits["M"], atoms["Minv"], 0),
        "m": (atoms["Minv"], named_bits["M"], 0),
    }

    def signed_return(matrix, matrix_inverse):
        for name in k2_names:
            image = bit_multiply(bit_multiply(matrix, named_bits[name]),
                                 matrix_inverse)
            sign = k2.get(image)
            if sign is None or sign != name.startswith("C"):
                return False
        return True

    start = (BIT_IDENTITY, BIT_IDENTITY, 0, "")
    queue = deque([start])
    seen = {(BIT_IDENTITY, 0)}
    odd_returns = []
    maximum_length = 6
    while queue:
        matrix, matrix_inverse, parity, word = queue.popleft()
        if word and parity and signed_return(matrix, matrix_inverse):
            odd_returns.append((len(word), word, matrix_order(matrix)))
            if len(odd_returns) >= 10:
                break
        if len(word) >= maximum_length:
            continue
        for letter, (generator, generator_inverse, toggle) in generators.items():
            if word and ((word[-1] == letter)
                         or (word[-1], letter) in (("M", "m"), ("m", "M"))):
                continue
            nxt = bit_multiply(matrix, generator)
            nxt_inverse = bit_multiply(generator_inverse, matrix_inverse)
            nxt_parity = parity ^ toggle
            key = (nxt, nxt_parity)
            if key not in seen:
                seen.add(key)
                queue.append((nxt, nxt_inverse, nxt_parity, word + letter))
    print("odd signed-K2 returns through length", maximum_length)
    print("states", len(seen), "returns", odd_returns)


if __name__ == "__main__":
    main()
