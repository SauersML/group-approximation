#!/usr/bin/env python3
"""Enumerate exact noncrossing one-copy cancellation trees for N0;511/I.

This is purely combinatorial: a block records syllables which must multiply
to the identity, except for one distinguished copy-0 block carrying the
outer boundary.  The coefficient words printed are in the five parameters
p,d,b,c,u after a=d*u*p^-1.
"""

from functools import lru_cache
from itertools import combinations
from math import gcd


SYLLABLES = (
    (3, "b^-1"), (2, "p"), (1, "d^-1"), (0, "c^-1*b"),
    (1, "c"), (2, "d"), (3, "p^-1*b^-1"), (2, "p"),
    (1, "d^-1"), (0, "c^-1*u^-1"), (1, "p^-1"), (2, "b"),
    (3, "c*b^-1"), (2, "p"), (1, "d^-1"),
    (0, "c^-1*d*u*p^-1"), (1, "b"), (2, "c"), (3, "d"),
)


@lru_cache(maxsize=None)
def partitions(indices):
    """All color-respecting noncrossing partitions of an index tuple."""
    if not indices:
        return ((),)
    first = indices[0]
    same = [i for i in indices[1:] if SYLLABLES[i][0] == SYLLABLES[first][0]]
    out = []
    # Select the rest of the block containing the first index.
    for width in range(len(same) + 1):
        for tail in combinations(same, width):
            block = (first,) + tail
            cuts = block + (indices[-1] + 1,)
            regions = []
            previous = first
            for cut in cuts[1:]:
                regions.append(tuple(i for i in indices if previous < i < cut))
                previous = cut
            choices = [partitions(region) for region in regions]
            products = [()]
            for choice in choices:
                products = [left + right for left in products for right in choice]
            out.extend(((block,) + rest) for rest in products)
    return tuple(out)


LETTERS = {
    "p": (1,), "d": (2,), "b": (3,), "c": (4,), "u": (5,),
    "p^-1": (-1,), "d^-1": (-2,), "b^-1": (-3,),
    "c^-1": (-4,), "u^-1": (-5,),
}


def reduce_word(word):
    out = []
    for letter in word:
        if out and out[-1] == -letter:
            out.pop()
        else:
            out.append(letter)
    return tuple(out)


def syllable_word(index):
    return reduce_word(sum((LETTERS[x] for x in SYLLABLES[index][1].split("*")), ()))


def block_tuple(block):
    return reduce_word(sum((syllable_word(i) for i in block), ()))


def inverse(word):
    return tuple(-x for x in reversed(word))


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


def tietze(relations, target):
    relations = [reduce_word(r) for r in relations if r]
    target = reduce_word(target)
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
            return tuple(sorted(set(relations))), target
        ri, generator, replacement = step
        relations.pop(ri)
        relations = [substitute(r, generator, replacement) for r in relations]
        relations = [r for r in relations if r]
        target = substitute(target, generator, replacement)


def forced_trivial(relations, target):
    if target in relations or inverse(target) in relations:
        return True
    if not target or len({abs(x) for x in target}) != 1:
        return False
    generator = abs(target[0])
    powers = []
    for relation in relations:
        if relation and all(abs(x) == generator for x in relation):
            powers.append(len(relation))
    order_bound = 0
    for power in powers:
        order_bound = gcd(order_bound, power)
    return order_bound == 1


def block_word(block):
    return " * ".join(SYLLABLES[i][1] for i in block)


def main():
    schemes = partitions(tuple(range(len(SYLLABLES))))
    total_targets = 0
    one_copy = set()
    for scheme in schemes:
        for target in scheme:
            total_targets += 1
            equations = tuple(block_tuple(block) for block in scheme if block != target)
            residual_relations, residual_target = tietze(equations, block_tuple(target))
            if residual_target:
                one_copy.add((tuple(target), residual_relations, residual_target))
    print(f"noncrossing_partitions={len(schemes)}")
    print(f"one_copy_target_schemes={total_targets}")
    print(f"tietze_nontrivial_target_schemes={len(one_copy)}")
    unresolved = [item for item in one_copy if not forced_trivial(item[1], item[2])]
    print(f"universally_unresolved_schemes={len(unresolved)}")
    for target, equations, residual_target in sorted(unresolved):
        print(f"TARGET {target}: {block_word(target)} => {residual_target}")
        print(f"  residual_relations={equations}")


if __name__ == "__main__":
    main()
