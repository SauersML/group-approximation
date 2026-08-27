"""Step 3 groundwork: the rank-five Steinberg relation family in atlas words.

Using the verified rank-five dictionary of `atlas_relator_rank5_dictionary`,
this emits the Steinberg / Cuntz-Krieger relation family among the 100
generators `x_kl(b)` of `St_5(L)`, translated into words in the twelve atlas
generators of `Pbar = K1 * K2`.  It mirrors, at rank five, the rank-three
family already in `atlas_two_chart_search.relation_family()`.

Each emitted word lies in `Rbar = ker(Pbar ->> Q)` -- verified here exactly by
binary Leavitt arithmetic, not assumed.  Writing `T_St` for the family, the
usability criterion of `atlas-relator-central-sufficiency` says `T_St` is a
usable relator list for the canonical regular-A8 criterion as soon as `T_St`
presents `St_5(L)` over the atlas: then `Rbar/<<T_St>> = K_2(5,L)`, which is
central in `St_5(L)` by Kervaire-Steinberg, so `Nbar <= <<T_St>>`.

Consistency check performed here.  By `atlas-kernel-window-length-nine`, every
usable list must contain a word outside `ker((p_1,p_2) : Pbar ->> A8 x A8)`.
So `T_St` MUST contain a relator with nontrivial factor projections.  If it did
not, either the dictionary or the relation family would be wrong.
"""

import argparse
import itertools
import json
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from atlas_kernel_collision_enumerator import (  # noqa: E402
    evaluate_word,
    factor_projections,
)
from atlas_relator_rank5_dictionary import (  # noqa: E402
    COEFF_LETTERS,
    rank5_word,
    transvection_lengths,
)
from atlas_two_chart_search import (  # noqa: E402
    I4,
    commutator,
    inverse,
    leavitt_is_one,
    product,
    reduce_word,
)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-triples", type=int, default=0,
                        help="smoke test: cap the number of index triples")
    parser.add_argument("--skip-orth", action="store_true")
    parser.add_argument("--emit", default="")
    args = parser.parse_args()

    lengths = transvection_lengths()
    memo = {}
    cache = {}

    def x(k, l, b):
        if (k, l, b) not in cache:
            cache[(k, l, b)] = rank5_word(k, l, b, memo)[0]
        return cache[(k, l, b)]

    names, words = [], []
    seen = set()

    def add(name, word):
        word = reduce_word(word)
        if not word:
            return
        key = tuple((f, bytes(g.reshape(-1))) for f, g in word)
        if key in seen:
            return
        seen.add(key)
        names.append(name)
        words.append(word)

    triples = [t for t in itertools.permutations(range(1, 6), 3)]
    if args.max_triples:
        triples = triples[:args.max_triples]
    print("index triples:", len(triples))

    for i, j, k in triples:
        for a in COEFF_LETTERS:
            add("stL_%d%d%d_%s" % (i, j, k, a),
                product(commutator(x(i, j, a), x(j, k, "1")),
                        inverse(x(i, k, a))))
            add("stR_%d%d%d_%s" % (i, j, k, a),
                product(commutator(x(i, j, "1"), x(j, k, a)),
                        inverse(x(i, k, a))))
        for left, right in (("E", "e"), ("F", "f")):
            add("cuntz_%d%d%d_%s%s" % (i, j, k, left, right),
                product(commutator(x(i, j, left), x(j, k, right)),
                        inverse(x(i, k, "1"))))
        for left, right in (("E", "f"), ("F", "e")):
            add("zero_%d%d%d_%s%s" % (i, j, k, left, right),
                commutator(x(i, j, left), x(j, k, right)))
        add("partition_%d%d%d" % (i, j, k),
            product(commutator(x(i, j, "e"), x(j, k, "E")),
                    commutator(x(i, j, "f"), x(j, k, "F")),
                    inverse(x(i, k, "1"))))

    if not args.skip_orth:
        roots = [(i, j) for i in range(1, 6) for j in range(1, 6) if i != j]
        for (i, j), (k, ell) in itertools.combinations(roots, 2):
            if i != ell and j != k:
                for a, b in (("1", "1"), ("e", "f"), ("E", "F")):
                    add("orth_%d%d_%d%d_%s%s" % (i, j, k, ell, a, b),
                        commutator(x(i, j, a), x(k, ell, b)))

    print("distinct nonidentity relators:", len(words))

    bad = []
    boundary = 0
    xlens, syls = [], []
    for name, word in zip(names, words):
        if not leavitt_is_one(evaluate_word(word)):
            bad.append(name)
        p1, p2 = factor_projections(word)
        if not (np.array_equal(p1, I4) and np.array_equal(p2, I4)):
            boundary += 1
        xlens.append(sum(lengths[m.tobytes()] for _f, m in word))
        syls.append(len(word))

    print("verified to lie in Rbar:", len(words) - len(bad), "of", len(words))
    if bad:
        print("NOT IN KERNEL:", bad[:10])
        return 1

    print("syllable length: min %d  max %d" % (min(syls), max(syls)))
    print("X-length:        min %d  max %d  total %d"
          % (min(xlens), max(xlens), sum(xlens)))
    print("relators with nontrivial (p1,p2): %d of %d" % (boundary, len(words)))
    if boundary:
        print("CONSISTENCY OK: the family escapes ker(Pbar ->> A8 x A8), as any")
        print("   usable list must (atlas-kernel-window-length-nine).")
    else:
        print("CONSISTENCY FAILURE: the whole family lies in the cartesian")
        print("   subgroup, so it cannot normally generate Nbar.")

    if args.emit:
        payload = [{"name": n,
                    "syllables": len(w),
                    "x_length": sum(lengths[m.tobytes()] for _f, m in w),
                    "word": [[int(f), int(np.packbits(m.reshape(-1))[0]) if False
                              else "".join(str(int(v)) for v in m.reshape(-1))]
                             for f, m in w]}
                   for n, w in zip(names, words)]
        with open(args.emit, "w") as handle:
            json.dump({"relators": payload}, handle, indent=1)
        print("wrote", args.emit)
    return 0


if __name__ == "__main__":
    sys.exit(main())
