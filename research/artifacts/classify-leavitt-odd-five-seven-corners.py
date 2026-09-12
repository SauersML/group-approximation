#!/usr/bin/env python3
"""Exact-witness screen for odd five/seven corner relations.

Run on MSI.  The screen is conservative: a word is rejected only when every
maximal G_0/G_1 syllable has an explicit moved basis vector in the faithful
infinite-word module.  The output lists the residual syllable words requiring
hand root reduction.
"""

from functools import lru_cache
from collections import Counter
import sys

N = 20
INVOLUTIONS = {"h0", "h2", "k0", "k1"}
ALPHABET = tuple(sorted((("h0", 1), ("h2", 1), ("k0", 1), ("k1", 1),
                         ("h1", 1), ("h1", -1),
                         ("k2", 1), ("k2", -1))))


def inverse(letter):
    name, sign = letter
    return (name, 1) if name in INVOLUTIONS else (name, -sign)


def canonical(word):
    rotations = [word[i:] + word[:i] for i in range(len(word))]
    inv = tuple(inverse(x) for x in reversed(word))
    rotations += [inv[i:] + inv[:i] for i in range(len(word))]
    return min(rotations)


def expand(letter):
    name, sign = letter
    atoms = {
        "h0": ((0, "a"),),
        "h2": ((0, "e"),),
        "k0": ((1, "a"),),
        "k1": ((1, "q"),),
        "h1": ((0, "q"), (1, "p")),
        "k2": ((0, "p"), (1, "e")),
    }[name]
    if sign == 1:
        return atoms
    return tuple((copy, token.swapcase() if token == "p" else token)
                 for copy, token in reversed(atoms))


def syllables(word):
    result = []
    for letter in word:
        for copy, token in expand(letter):
            if result and result[-1][0] == copy:
                result[-1][1].append(token)
            else:
                result.append([copy, [token]])
    return tuple((copy, tuple(tokens)) for copy, tokens in result)


def simplify_tokens(tokens):
    """Use only exact relations in <a,e,q> = C2^3 and pP=Pp=1."""
    old = None
    tokens = tuple(tokens)
    while tokens != old:
        old = tokens
        pieces = []
        root_segment = []

        def flush():
            if root_segment:
                parity = {x: root_segment.count(x) % 2 for x in ("a", "e", "q")}
                pieces.extend(x for x in ("a", "e", "q") if parity[x])
                root_segment.clear()

        for token in tokens:
            if token in ("a", "e", "q"):
                root_segment.append(token)
            else:
                flush()
                if pieces and ((pieces[-1], token) in (("p", "P"), ("P", "p"))):
                    pieces.pop()
                else:
                    pieces.append(token)
        flush()
        tokens = tuple(pieces)
    return tokens


def reduced_syllables(word):
    blocks = [[copy, list(tokens)] for copy, tokens in syllables(word)]
    changed = True
    while changed:
        changed = False
        next_blocks = []
        for copy, tokens in blocks:
            tokens = list(simplify_tokens(tokens))
            if not tokens:
                changed = True
                continue
            if next_blocks and next_blocks[-1][0] == copy:
                next_blocks[-1][1].extend(tokens)
                changed = True
            else:
                next_blocks.append([copy, tokens])
        blocks = next_blocks
    return tuple((copy, tuple(simplify_tokens(tokens))) for copy, tokens in blocks)


def normalize(prefix, tail):
    while prefix and prefix[-1] == tail:
        prefix = prefix[:-1]
    return prefix, tail


ROOT = {"a": ("s", "0"), "b": ("s", "1"),
        "c": ("t", "0"), "e": ("t", "1")}


def ring_action(kind, bit, word):
    prefix, tail = word
    if kind == "s":
        return normalize(bit + prefix, tail)
    first = prefix[0] if prefix else tail
    if first != bit:
        return None
    return normalize(prefix[1:] if prefix else "", tail)


def toggle(values, value):
    if value in values:
        values.remove(value)
    else:
        values.add(value)


ROOT_FACTORS = {
    "a": (("r", "a", 0, 1),),
    "e": (("r", "e", 0, 1),),
    "q": (("r", "b", 2, 3), ("r", "c", 10, 11)),
    "p": (("p", 1),),
    "P": (("p", -1),),
}


def act(factor, vector):
    if factor[0] == "p":
        return {((coordinate + factor[1]) % N, word)
                for coordinate, word in vector}
    _, letter, i, j = factor
    result = set(vector)
    root_kind, bit = ROOT[letter]
    for coordinate, word in vector:
        if coordinate == j:
            image = ring_action(root_kind, bit, word)
            if image is not None:
                toggle(result, (i, image))
    return result


def evaluate(tokens, vector):
    factors = sum((ROOT_FACTORS[token] for token in tokens), ())
    for factor in reversed(factors):
        vector = act(factor, vector)
    return vector


TESTS = tuple(
    {(coordinate, normalize(prefix, tail))}
    for coordinate in range(N)
    for tail in "01"
    for prefix in ("", "0", "1", "01", "10", "001", "110", "0101")
)


@lru_cache(None)
def witnessed_nonidentity(tokens):
    return any(evaluate(tokens, test) != test for test in TESTS)


def necklaces(length, alphabet_size):
    """Rotation-minimal necklaces (Fredricksen--Kessler--Maiorana)."""
    a = [0] * (length + 1)

    def generate(t, period):
        if t > length:
            if length % period == 0:
                yield tuple(a[1:])
            return
        a[t] = a[t - period]
        yield from generate(t + 1, period)
        for value in range(a[t - period] + 1, alphabet_size):
            a[t] = value
            yield from generate(t + 1, t)

    yield from generate(1, 1)


def words(length):
    for indices in necklaces(length, len(ALPHABET)):
        word = tuple(ALPHABET[i] for i in indices)
        if any(word[(i + 1) % length] == inverse(word[i])
               for i in range(length)):
            continue
        if word != canonical(word):
            continue
        yield word


lengths = tuple(map(int, sys.argv[1:])) or (5, 7)
for length in lengths:
    total = 0
    survivors = []
    unknown_blocks = Counter()
    for word in words(length):
        total += 1
        blocks = reduced_syllables(word)
        unknown = [tokens for _, tokens in blocks
                   if not witnessed_nonidentity(tokens)]
        if unknown:
            survivors.append((word, blocks))
            unknown_blocks.update(unknown)
    print("LENGTH", length, "ORBIT_REPRESENTATIVES", total)
    print("CONSERVATIVE_SURVIVORS", len(survivors))
    print("UNKNOWN_BLOCKS", len(unknown_blocks))
    for block, count in unknown_blocks.most_common():
        print("BLOCK", block, count)
    for word, blocks in survivors[:100]:
        print("SURVIVOR", word, blocks)
