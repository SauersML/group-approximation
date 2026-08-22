#!/usr/bin/env python3
"""Enumerate only maximal noncrossing schemes for inverse I1;412 Eq3."""

from functools import lru_cache
from itertools import combinations, product


COLORS = (3, 2, 1, 2, 1, 2, 1, 2, 1, 0, 1, 0, 1, 0, 1,
          2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 0, 1, 2, 3)

# g1,g2,g4,...,g13 are numbered 1,...,12; g0=g3=1 already.  Keep
# the raw names beside the compressed integers: the previous version of this
# screen had an off-by-one generator map, and these assertions are the cheap
# one-hot replay that prevents such a result from entering Cairn again.
GENERATORS = ("g1", "g2", "g4", "g5", "g6", "g7", "g8", "g9",
              "g10", "g11", "g12", "g13")
NUMBER = {name: index + 1 for index, name in enumerate(GENERATORS)}
RAW_S = (
    (("g10", -1),), (("g9", -1),), (("g8", -1),), (("g7", -1),),
    (("g6", -1),), (("g5", -1),), (("g4", -1), ("g2", -1)),
    (("g1", -1), ("g13", -1)), (("g12", -1),),
    (("g11", -1), ("g4", 1)), (("g5", 1),), (("g6", 1),),
    (("g7", 1),), (("g8", 1),), (("g9", 1),), (("g10", 1),),
    (("g11", 1), ("g10", -1)), (("g9", -1),), (("g8", -1),),
    (("g7", -1),), (("g6", -1),), (("g5", -1),),
    (("g4", -1), ("g2", -1)), (("g1", -1), ("g13", -1)),
    (("g12", -1),), (("g11", -1), ("g9", 1)), (("g10", 1),),
    (("g11", 1),), (("g12", 1),),
)
S = ((-9,), (-8,), (-7,), (-6,), (-5,), (-4,), (-3, -2),
     (-1, -12), (-11,), (-10, 3), (4,), (5,), (6,), (7,), (8,),
     (9,), (10, -9), (-8,), (-7,), (-6,), (-5,), (-4,),
     (-3, -2), (-1, -12), (-11,), (-10, 8), (9,), (10,), (11,))

assert S == tuple(tuple(sign * NUMBER[name] for name, sign in syllable)
                  for syllable in RAW_S)
assert len(S) == len(COLORS)


@lru_cache(maxsize=None)
def maximal(lo, hi):
    if lo == hi:
        return (0, ((),))
    candidates = [i for i in range(lo + 1, hi)
                  if COLORS[i] == COLORS[lo]]
    best = hi - lo + 1
    winners = set()
    for width in range(len(candidates) + 1):
        for tail in combinations(candidates, width):
            block = (lo,) + tail
            bounds = block + (hi,)
            pieces = [maximal(left + 1, right)
                      for left, right in zip(bounds, bounds[1:])]
            score = 1 + sum(piece[0] for piece in pieces)
            if score > best:
                continue
            if score < best:
                best, winners = score, set()
            for choices in product(*(piece[1] for piece in pieces)):
                winners.add(tuple(sorted((block,) + sum(choices, ()))))
    return best, tuple(sorted(winners))


def reduce_word(word):
    out = []
    for letter in word:
        if out and out[-1] == -letter:
            out.pop()
        else:
            out.append(letter)
    return tuple(out)


def inverse(word):
    return tuple(-letter for letter in reversed(word))


def substitute(word, generator, replacement):
    out = ()
    for letter in word:
        if letter == generator:
            out = reduce_word(out + replacement)
        elif letter == -generator:
            out = reduce_word(out + inverse(replacement))
        else:
            out = reduce_word(out + (letter,))
    return out


def tietze(relations):
    relations = [reduce_word(relation) for relation in relations if relation]
    while True:
        step = None
        for ri, relation in enumerate(relations):
            for pos, letter in enumerate(relation):
                generator = abs(letter)
                if sum(abs(x) == generator for x in relation) == 1:
                    left, right = relation[:pos], relation[pos + 1:]
                    replacement = (inverse(left) + inverse(right)
                                   if letter > 0 else right + left)
                    step = ri, generator, reduce_word(replacement)
                    break
            if step:
                break
        if not step:
            return tuple(sorted(set(relations)))
        ri, generator, replacement = step
        relations.pop(ri)
        relations = [substitute(r, generator, replacement) for r in relations]
        relations = [r for r in relations if r]


def main():
    count, schemes = maximal(0, len(COLORS))
    print(f"minimum_blocks={count}")
    print(f"maximal_schemes={len(schemes)}")
    presentations = set()
    for scheme in schemes:
        relations = [reduce_word(sum((S[index] for index in block), ()))
                     for block in scheme]
        presentations.add(tietze(relations))
    print(f"tietze_presentations={len(presentations)}")
    for presentation in sorted(presentations)[:100]:
        print(presentation)


if __name__ == "__main__":
    main()
