"""Enumerate short exact relators in ``<P,J1,x_78(1),x_87(1)>``.

Run only through MSI.  Products use faithful sparse Leavitt normal forms.
The bounded enumeration calibrates, but does not prove, the all-word corner
retraction recorded in Cairn.
"""

import argparse

from endpoint_chain_center_hecke_collision_audit import coeff, whitehead
from signed_hecke_literal_pauli_probe_audit import (
    identity_matrix,
    matrices_equal,
    matrix_multiply,
    word_matrix,
)


IDENTITY = identity_matrix()
NAMES = ("P", "J", "n", "m")


def root(target, source):
    return word_matrix(((source, target, coeff("", "")),))


GENERATORS = (
    word_matrix(whitehead(8, 2, 2)),
    word_matrix(whitehead(7, 8, 1)),
    root(7, 8),
    root(8, 7),
)


def canonical_cycle(word):
    rotations = []
    for candidate in (word, tuple(reversed(word))):
        rotations.extend(
            candidate[index:] + candidate[:index]
            for index in range(len(candidate))
        )
    return min(rotations)


def display(word):
    return "".join(NAMES[index] for index in word)


def involutive_reduce(word):
    stack = []
    for letter in word:
        if stack and stack[-1] == letter:
            stack.pop()
        else:
            stack.append(letter)
    return tuple(stack)


def enumerate_relators(maximum_length):
    relators = set()
    level_counts = {}

    def visit(word, value):
        length = len(word)
        if length >= 2 and word[0] != word[-1] and matrices_equal(value, IDENTITY):
            relator = canonical_cycle(word)
            relators.add(relator)
            level_counts[length] = level_counts.get(length, 0) + 1
        if length == maximum_length:
            return
        for index, generator in enumerate(GENERATORS):
            if word and word[-1] == index:
                continue
            visit(word + (index,), matrix_multiply(value, generator))

    visit((), IDENTITY)
    return relators, level_counts


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, default=10)
    arguments = parser.parse_args()
    relators, level_counts = enumerate_relators(arguments.depth)
    print("maximum freely reduced length", arguments.depth)
    print("identity hits by length", tuple(sorted(level_counts.items())))
    print("cyclic relators", tuple(display(word) for word in sorted(relators)))
    print(
        "P=J=1 involutive reductions",
        tuple(
            (display(word), display(involutive_reduce(tuple(x for x in word if x >= 2))))
            for word in sorted(relators)
        ),
    )


if __name__ == "__main__":
    main()
