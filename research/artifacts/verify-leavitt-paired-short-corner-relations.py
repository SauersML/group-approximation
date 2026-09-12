#!/usr/bin/env python3
"""Exact short-corner and formal-overlap census for the paired L6 quotient.

Nonidentity of a coefficient block is certified on the faithful standard
module of the binary Leavitt algebra.  Its basis consists of infinite binary
words.  Here such a word is represented exactly as an eventually constant
tail, not by a finite truncation.
"""

from itertools import product

N = 20


def normalize(prefix, tail):
    while prefix and prefix[-1] == tail:
        prefix = prefix[:-1]
    return prefix, tail


def prepend(bit, word):
    prefix, tail = word
    return normalize(bit + prefix, tail)


def delete(bit, word):
    prefix, tail = word
    first = prefix[0] if prefix else tail
    if first != bit:
        return None
    return normalize(prefix[1:] if prefix else "", tail)


def toggle(values, value):
    if value in values:
        values.remove(value)
    else:
        values.add(value)


ROOT = {"a": ("s", "0"), "b": ("s", "1"),
        "c": ("t", "0"), "e": ("t", "1")}


def generator_action(letter, inverse, vector):
    if letter == "d":
        shift = -1 if inverse else 1
        return {((coordinate + shift) % N, word) for coordinate, word in vector}

    # Every elementary root x_12(q) has order two in characteristic two.
    kind, bit = ROOT[letter]
    result = set(vector)
    for coordinate, word in vector:
        if coordinate != 1:
            continue
        image = prepend(bit, word) if kind == "s" else delete(bit, word)
        if image is not None:
            toggle(result, (0, image))
    return result


def block_is_detectably_nontrivial(block):
    tests = []
    for coordinate in range(N):
        for tail in "01":
            for prefix in ("", "0", "1", "01", "10", "001", "110"):
                tests.append((coordinate, normalize(prefix, tail)))
    for test in tests:
        vector = {test}
        # Left-to-right group word acts right-to-left.
        for letter, inverse in reversed(block):
            vector = generator_action(letter, inverse, vector)
        if vector != {test}:
            return True
    return False


# Each corner is a word in the indicated free factor G_0 or G_1.
CORNERS = {
    "h0": ((0, "a"), (1, "b")),
    "h1": ((0, "c"), (1, "d")),
    "h2": ((0, "e"),),
    "k0": ((1, "a"),),
    "k1": ((0, "b"), (1, "c")),
    "k2": ((0, "d"), (1, "e")),
}


def expand(token):
    name, sign = token
    letters = CORNERS[name]
    if sign < 0:
        letters = tuple(reversed(letters))
    return tuple((copy, letter, sign < 0) for copy, letter in letters)


def relation_is_detected(tokens):
    letters = sum((expand(token) for token in tokens), ())
    blocks = []
    for copy, letter, inverse in letters:
        if blocks and blocks[-1][0] == copy:
            blocks[-1][1].append((letter, inverse))
        else:
            blocks.append((copy, [(letter, inverse)]))

    # In a free product, a nontrivial block certifies a nontrivial reduced word.
    # Iteratively erase blocks which are exact square cancellations.  Any other
    # block below is certified nontrivial by an exact infinite-word witness.
    def cancel_block(block):
        stack = []
        for letter, inverse in block:
            if stack and stack[-1][0] == letter and (
                    letter != "d" or stack[-1][1] != inverse):
                stack.pop()
            else:
                stack.append((letter, inverse))
        return stack

    changed = True
    while changed and blocks:
        changed = False
        kept = []
        for copy, block in blocks:
            reduced = cancel_block(block)
            if not reduced:
                changed = True
                continue
            if reduced != block:
                changed = True
            kept.append((copy, reduced))
        blocks = kept
        if changed:
            merged = []
            for copy, block in blocks:
                if merged and merged[-1][0] == copy:
                    merged[-1][1].extend(block)
                else:
                    merged.append((copy, block))
            blocks = merged

    if not blocks:
        return True
    # Every surviving free-factor block must itself be certified nonidentity;
    # then the free-product normal form is nonempty.
    assert all(block_is_detectably_nontrivial(block) for _, block in blocks), tokens
    return False


TOKENS = tuple((name, sign) for name in CORNERS for sign in (1, -1))


def formal_inverse(token):
    return token[0], -token[1]


def cyclically_formally_reduced(tokens):
    return all(tokens[(i + 1) % len(tokens)] != formal_inverse(tokens[i])
               for i in range(len(tokens)))


relations = {}
for length in range(1, 5):
    found = []
    for tokens in product(TOKENS, repeat=length):
        if cyclically_formally_reduced(tokens) and relation_is_detected(tokens):
            found.append(tokens)
    relations[length] = found

assert not relations[1]
assert len(relations[2]) == 4
assert all(word[0][0] == word[1][0] in {"h2", "k0"}
           for word in relations[2])
assert not relations[3]

# Every length-four relation splits cyclically into two of the square gates.
def square_gate(pair):
    return pair[0][0] == pair[1][0] in {"h2", "k0"}


assert relations[4]
assert all(any(square_gate((word[i], word[(i + 1) % 4])) and
               square_gate((word[(i + 2) % 4], word[(i + 3) % 4]))
               for i in range(4)) for word in relations[4])


# Literal syllable overlaps in the symmetrized pair.  Coefficient inverses are
# kept formal, except for the two proved involutions h2 and k0.
R0 = (("h0", 1), ("z", 1), ("h1", 1), ("z", 1),
      ("h2", 1), ("z", -1))
R1 = (("k0", 1), ("z", 1), ("k1", 1), ("z", 1),
      ("k2", 1), ("z", -1))


def inverse_syllable(syllable):
    name, sign = syllable
    if name in {"h2", "k0"}:
        return name, 1
    return name, -sign


def inverse_word(word):
    return tuple(inverse_syllable(syllable) for syllable in reversed(word))


symmetrized = []
for relator, word in enumerate((R0, R1)):
    for orientation, oriented in ((1, word), (-1, inverse_word(word))):
        for shift in range(6):
            symmetrized.append((relator, orientation, shift,
                                oriented[shift:] + oriented[:shift]))

maximal = []
for left_index, left in enumerate(symmetrized):
    for right in symmetrized[left_index + 1:]:
        if left[3] == right[3]:
            continue
        length = 0
        while length < 6 and left[3][length] == right[3][length]:
            length += 1
        if length:
            maximal.append((length, left[:3], right[:3], left[3][:length]))

long = [entry for entry in maximal if entry[0] > 1]
assert len(long) == 4
assert {entry[3] for entry in long} == {
    (("h2", 1), ("z", -1)),
    (("z", 1), ("h2", 1), ("z", -1)),
    (("k0", 1), ("z", 1)),
    (("z", -1), ("k0", 1), ("z", 1)),
}

print("PASS: short coefficient regions are generated by h2^2 and k0^2")
print("PASS: the only multi-syllable symmetrized overlaps are the four")
print("      subwords of z h2 z^-1 and z^-1 k0 z")
