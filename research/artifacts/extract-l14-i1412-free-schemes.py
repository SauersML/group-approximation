#!/usr/bin/env python3
"""Print representative free Tietze schemes for corrected inverse I1;412.

This is a certificate extractor for the two audited maximal-scheme screens.
It deliberately stops after a small fixed number of representatives and emits
the original block relations, before Tietze substitutions erase their labels.
"""

import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


EQ3 = load("i1412_eq3", "enumerate-l14-i1412-eq3-maximal.py")
EQ1 = load("i1412_eq1", "enumerate-l14-i1412-eq1-maximal.py")


def extract(label, colors, syllables, machinery, limit=8):
    machinery.COLORS = colors
    machinery.maximal.cache_clear()
    count, schemes = machinery.maximal(0, len(colors))
    print(f"[{label}] minimum_blocks={count} maximal_schemes={len(schemes)}")
    found = 0
    for scheme in schemes:
        relations = tuple(
            machinery.reduce_word(
                sum((syllables[index] for index in block), ())
            )
            for block in scheme
        )
        relations = tuple(relation for relation in relations if relation)
        if machinery.tietze(relations):
            continue
        print(f"[{label}] free_scheme={scheme}")
        print(f"[{label}] raw_relations={relations}")
        found += 1
        if found == limit:
            break
    print(f"[{label}] representatives={found}")


def main():
    extract("eq3", EQ3.COLORS, EQ3.S, EQ3)
    extract("eq1", EQ1.COLORS, EQ1.S, EQ1.EQ3)


if __name__ == "__main__":
    main()
