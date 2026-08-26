"""The involutivity relators `x_ij(a)^2`, and the enlarged `T_St`.

Why these are needed.  `notes/STEINBERG_SPARE_INDEX_2026-08-15.md` §8 closes
spare-index independence but isolates a genuine defect of the emitted family:
`Ehat_ij` must be a homomorphism `(L,+) -> G_0`, so over `F2` it needs
`Ehat_ij(a)^2 = Ehat_ij(a+a) = 1`.  That does NOT follow from the emitted
relations, and the note gives the reason: `L_Z(1,2)` satisfies the same five
Cuntz-Krieger relations (which carry no characteristic assumption) and is a
free `Z`-module, so `St_5(L_Z)` receives a homomorphism from `G_0` sending
`X_ij(1)^2` to `E_ij(2) != 1`.  The canonical two-letter words are built by
`root_word` as purely multiplicative nested commutators, so they lift, and the
counterexample stands.

The repair is the 100 relators `x_ij(a)^2` over the 20 roots and the five
letters.  They lie in `Rbar` because each `x_ij(a)` evaluates to `1 + m` with
`m = d_{E_i} a d_{E_j}^*` and `m^2 = 0` (the leaves `E_i`, `E_j` are distinct
members of a prefix code, so `d_{E_j}^* d_{E_i} = 0`), whence
`x_ij(a)^2 = 1 + m^2 = 1` over `F2`.  That argument is NOT assumed here: every
square is evaluated exactly and checked against the identity.

Relators whose word reduces to the empty word are already trivial in `Pbar`
itself -- that happens exactly when the dictionary word is a single chart
syllable, which is an involution in `GL_4(F2)` -- and are reported separately.
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
    leavitt_is_one,
    product,
    reduce_word,
)


def word_to_json(word, lengths):
    return {"syllables": len(word),
            "x_length": sum(lengths[m.tobytes()] for _f, m in word),
            "word": [[int(f), "".join(str(int(v)) for v in m.reshape(-1))]
                     for f, m in word]}


def generate_relators(verify=True):
    """Return nontrivial square relators and freely trivial names."""
    lengths = transvection_lengths()
    memo = {}

    nontrivial, trivial = [], []
    not_in_kernel = []
    for i, j in itertools.permutations(range(1, 6), 2):
        for a in COEFF_LETTERS:
            base = rank5_word(i, j, a, memo)[0]
            square = reduce_word(product(base, base))
            name = "inv_%d%d_%s" % (i, j, a)
            if not square:
                trivial.append((name, len(base)))
                continue
            if verify and not leavitt_is_one(evaluate_word(square)):
                not_in_kernel.append(name)
            nontrivial.append((name, square))

    if not_in_kernel:
        raise AssertionError("involutivity words outside Rbar: %r"
                             % not_in_kernel[:10])
    return nontrivial, trivial, lengths


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--emit", default="")
    parser.add_argument("--merge", default="",
                        help="existing family JSON to union with")
    parser.add_argument("--emit-merged", default="")
    args = parser.parse_args()

    nontrivial, trivial, lengths = generate_relators(verify=True)
    not_in_kernel = []

    total = len(nontrivial) + len(trivial)
    print("involutivity relators considered:", total)
    print("  reduce to the empty word in Pbar (already trivial):",
          len(trivial))
    print("  nontrivial words emitted:                          ",
          len(nontrivial))
    print("  verified to lie in Rbar:                           ",
          len(nontrivial) - len(not_in_kernel), "of", len(nontrivial))
    if trivial:
        base_syllables = sorted({s for _n, s in trivial})
        print("  (the trivial ones are exactly the single-syllable dictionary")
        print("   words, whose chart transvection squares to the identity;")
        print("   base syllable lengths seen:", base_syllables, ")")

    if nontrivial:
        syl = [len(w) for _n, w in nontrivial]
        xln = [sum(lengths[m.tobytes()] for _f, m in w) for _n, w in nontrivial]
        print("syllable length: min %d  max %d" % (min(syl), max(syl)))
        print("X-length:        min %d  max %d  total %d"
              % (min(xln), max(xln), sum(xln)))
        escaping = 0
        for _n, w in nontrivial:
            p1, p2 = factor_projections(w)
            if not (np.array_equal(p1, I4) and np.array_equal(p2, I4)):
                escaping += 1
        print("relators with nontrivial (p1,p2): %d of %d"
              % (escaping, len(nontrivial)))

    payload = [dict(name=n, **word_to_json(w, lengths)) for n, w in nontrivial]

    if args.emit:
        with open(args.emit, "w") as handle:
            json.dump({"relators": payload}, handle)
        print("wrote", args.emit)

    if args.merge:
        with open(args.merge) as handle:
            existing = json.load(handle)["relators"]
        seen = {tuple(tuple(x) for x in entry["word"]) for entry in existing}
        added = [entry for entry in payload
                 if tuple(tuple(x) for x in entry["word"]) not in seen]
        merged = existing + added
        print("merge: %d existing + %d new (%d already present) = %d"
              % (len(existing), len(added), len(payload) - len(added),
                 len(merged)))
        if args.emit_merged:
            with open(args.emit_merged, "w") as handle:
                json.dump({"relators": merged}, handle)
            print("wrote", args.emit_merged)
    return 0


if __name__ == "__main__":
    sys.exit(main())
