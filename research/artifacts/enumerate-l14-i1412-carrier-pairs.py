#!/usr/bin/env python3
"""Intersect the two audited inverse I1;412 carrier equations exactly.

The key point is to retain every Tietze substitution on the twelve original
coefficient generators.  Merely intersecting the 116 and 47 abstract residual
presentations is invalid because their eliminated generators need not use the
same change of variables.
"""

import importlib.util
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


EQ3 = load("i1412_eq3", "enumerate-l14-i1412-eq3-maximal.py")
EQ1 = load("i1412_eq1", "enumerate-l14-i1412-eq1-maximal.py")
GENERATOR_COUNT = len(EQ3.GENERATORS)


def schemes(colors):
    @lru_cache(maxsize=None)
    def visit(lo, hi):
        if lo == hi:
            return 0, ((),)
        candidates = [i for i in range(lo + 1, hi)
                      if colors[i] == colors[lo]]
        best, winners = hi - lo + 1, set()
        for width in range(len(candidates) + 1):
            for tail in combinations(candidates, width):
                block = (lo,) + tail
                bounds = block + (hi,)
                pieces = [visit(left + 1, right)
                          for left, right in zip(bounds, bounds[1:])]
                score = 1 + sum(piece[0] for piece in pieces)
                if score > best:
                    continue
                if score < best:
                    best, winners = score, set()
                for choices in product(*(piece[1] for piece in pieces)):
                    winners.add(tuple(sorted((block,) + sum(choices, ()))))
        return best, tuple(sorted(winners))

    return visit(0, len(colors))


def initial_images():
    return tuple((generator,) for generator in range(1, GENERATOR_COUNT + 1))


def normalize_relations(relations):
    return tuple(sorted(set(EQ3.reduce_word(relation)
                            for relation in relations if relation)))


def close_tietze(relations, images):
    relations = list(normalize_relations(relations))
    images = list(images)
    while True:
        step = None
        for ri, relation in enumerate(relations):
            for pos, letter in enumerate(relation):
                generator = abs(letter)
                if sum(abs(x) == generator for x in relation) == 1:
                    left, right = relation[:pos], relation[pos + 1:]
                    replacement = (EQ3.inverse(left) + EQ3.inverse(right)
                                   if letter > 0 else right + left)
                    step = ri, generator, EQ3.reduce_word(replacement)
                    break
            if step:
                break
        if not step:
            return normalize_relations(relations), tuple(images)
        ri, generator, replacement = step
        relations.pop(ri)
        relations = [EQ3.substitute(r, generator, replacement)
                     for r in relations]
        relations = [r for r in relations if r]
        images = [EQ3.substitute(word, generator, replacement)
                  for word in images]


def transform(word, images):
    out = ()
    for letter in word:
        image = images[abs(letter) - 1]
        if letter < 0:
            image = EQ3.inverse(image)
        out = EQ3.reduce_word(out + image)
    return out


def transformed_free_product(colors, syllables, images):
    out = []
    for color, syllable in zip(colors, syllables):
        coefficient = transform(syllable, images)
        if not coefficient:
            continue
        if out and out[-1][0] == color:
            product_word = EQ3.reduce_word(out[-1][1] + coefficient)
            out.pop()
            if product_word:
                out.append((color, product_word))
        else:
            out.append((color, coefficient))
    return tuple(out)


def block_relations(scheme, syllables):
    return tuple(EQ3.reduce_word(sum((syllables[index] for index in block), ()))
                 for block in scheme)


def carrier_states(report=False):
    _, eq3_schemes = schemes(EQ3.COLORS)
    eq3_states = set()
    for scheme in eq3_schemes:
        relations = block_relations(scheme, EQ3.S)
        eq3_states.add(close_tietze(relations, initial_images()))
    if report:
        print(f"eq3_substitution_states={len(eq3_states)}", flush=True)

    transformed_inputs = {}
    for residual, images in eq3_states:
        word = transformed_free_product(EQ1.COLORS, EQ1.S, images)
        transformed_inputs.setdefault((residual, word), images)
    if report:
        print(f"distinct_transformed_eq1_inputs={len(transformed_inputs)}", flush=True)

    combined = set()
    scheme_total = 0
    for input_index, ((residual, word), images) in enumerate(
            transformed_inputs.items(), 1):
        colors = tuple(color for color, _ in word)
        syllables = tuple(syllable for _, syllable in word)
        _, eq1_schemes = schemes(colors)
        scheme_total += len(eq1_schemes)
        for scheme in eq1_schemes:
            relations = residual + block_relations(scheme, syllables)
            combined.add(close_tietze(relations, images))
        if report and input_index % 100 == 0:
            print(f"processed={input_index} combined={len(combined)}", flush=True)
    if report:
        print(f"transformed_eq1_schemes={scheme_total}")
        print(f"combined_substitution_states={len(combined)}")
        print(f"combined_abstract_presentations={len(set(r for r, _ in combined))}")
    return combined


def main():
    combined = carrier_states(report=True)
    for residual, images in sorted(combined)[:20]:
        print((residual, images))


if __name__ == "__main__":
    main()
