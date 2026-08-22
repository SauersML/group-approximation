#!/usr/bin/env python3
"""Audit min=max for every Eq3-transformed inverse I1;412 Eq1 word."""

import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PAIRS = load("i1412_pairs", "enumerate-l14-i1412-carrier-pairs.py")
FORESTS = load("maximal_nc_forests", "enumerate-maximal-noncrossing-forests.py")
EQ3 = PAIRS.EQ3
EQ1 = PAIRS.EQ1


def main():
    _, eq3_schemes = PAIRS.schemes(EQ3.COLORS)
    eq3_states = set()
    for scheme in eq3_schemes:
        relations = PAIRS.block_relations(scheme, EQ3.S)
        eq3_states.add(PAIRS.close_tietze(relations, PAIRS.initial_images()))

    transformed_inputs = {}
    for residual, images in eq3_states:
        word = PAIRS.transformed_free_product(EQ1.COLORS, EQ1.S, images)
        transformed_inputs.setdefault((residual, word), images)

    failures = []
    maximal_total = 0
    minimum_total = 0
    for index, ((residual, word), images) in enumerate(
            sorted(transformed_inputs.items()), 1):
        colors = tuple(color for color, _ in word)
        minimum_count, minimum_schemes = PAIRS.schemes(colors)
        maximal_schemes, _ = FORESTS.maximal_forests(colors)
        minimum_set = set(minimum_schemes)
        maximal_set = set(maximal_schemes)
        minimum_total += len(minimum_set)
        maximal_total += len(maximal_set)
        extra = sorted(maximal_set - minimum_set)
        if extra:
            histogram = {}
            for scheme in maximal_set:
                histogram[len(scheme)] = histogram.get(len(scheme), 0) + 1
            failures.append((index, minimum_count, histogram, residual,
                             word, images, extra[0]))

    print(f"transformed_inputs={len(transformed_inputs)}")
    print(f"minimum_schemes_total={minimum_total}")
    print(f"maximal_schemes_total={maximal_total}")
    print(f"nonminimum_maximal_inputs={len(failures)}")
    for failure in failures[:20]:
        print("FAIL", failure)


if __name__ == "__main__":
    main()

