"""Step 4 validation: run the finite-quotient screens on an emitted relator list.

The extraction program's own acceptance test is that any candidate list `T_St`
must SURVIVE the finite-quotient screens -- a list killed by a homomorphism
onto a nontrivial finite group cannot have `Nbar <= <<T_St>>`, so it would be
wrong.  This runs the two screens directly on a list emitted by
`atlas_relator_rank5_full_family.py` (or `..._relations.py`) rather than on the
enumerated kernel windows.

Screens:
  (D) the retraction `(p_1,p_2) : A8 * A8 ->> A8 x A8`;
  (A) every pair of injective `A8 -> A_m` up to global conjugacy, `m <= 11`.

For (A) the stage-one filter cannot reuse the radius-2 commuting conditions, so
the shortest relators of the list are used as the filter instead: a candidate
must kill all of them before the full list is evaluated.
"""

import argparse
import json
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from atlas_relator_a9_screen import (  # noqa: E402
    GENS,
    coset_permutation_table,
    find_index_eight_subgroup,
    generated_subgroup,
    perm_mul,
)
from atlas_relator_alternating_screen import all_even_permutations, widen  # noqa: E402
from atlas_two_chart_search import I4, gf2_inv, gf2_mul  # noqa: E402


def load(pathname):
    with open(pathname) as handle:
        payload = json.load(handle)
    words = []
    for entry in payload["relators"]:
        word = []
        for factor, bits in entry["word"]:
            matrix = np.array([int(ch) for ch in bits],
                              dtype=np.uint8).reshape(4, 4)
            word.append((int(factor), matrix))
        words.append((entry["name"], word))
    return words


def projections(word):
    out = []
    for selected in (1, 2):
        value = I4.copy()
        for factor, matrix in word:
            if factor == selected:
                value = gf2_mul(value, matrix)
        out.append(value)
    return out


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("list_json")
    parser.add_argument("--degree", type=int, default=10)
    parser.add_argument("--filter-size", type=int, default=40)
    args = parser.parse_args()

    words = load(args.list_json)
    print("relators loaded:", len(words))

    escaping = 0
    for _name, word in words:
        p1, p2 = projections(word)
        if not (np.array_equal(p1, I4) and np.array_equal(p2, I4)):
            escaping += 1
    print("SCREEN (D): %d of %d escape ker(Pbar ->> A8 x A8)"
          % (escaping, len(words)))
    if escaping == 0:
        print("   FAILS -- the whole list lies in the cartesian subgroup")
        return 1
    print("   passes")

    m = args.degree
    elements = generated_subgroup(GENS)
    iota = widen(coset_permutation_table(
        elements, find_index_eight_subgroup(elements, 0)), m)
    iota_graph = {key: iota[gf2_inv(g).T.copy().tobytes()]
                  for key, g in elements.items()}

    ordered = sorted(words, key=lambda item: len(item[1]))
    filt = ordered[:args.filter_size]
    print("stage-1 filter: %d shortest relators (syllables %d..%d)"
          % (len(filt), len(filt[0][1]), len(filt[-1][1])))

    D = all_even_permutations(m)
    Dinv = np.argsort(D, axis=1).astype(np.int8)
    identity = np.arange(m, dtype=np.int8)
    print("|A%d| candidates per twist: %d" % (m, len(D)))

    survivors = []
    for twist in (False, True):
        table = iota_graph if twist else iota
        alive = np.ones(len(D), dtype=bool)
        for _name, word in filt:
            if not alive.any():
                break
            value = np.tile(identity, (len(D), 1))
            for factor, matrix in word:
                key = matrix.tobytes()
                # words compose left to right: value <- value . letter,
                # matching perm_mul(p, q) = p[q] used everywhere else here.
                if factor == 1:
                    value = value[:, iota[key]]
                else:
                    conj = np.take_along_axis(D, table[key][Dinv], axis=1)
                    value = np.take_along_axis(value, conj, axis=1)
            alive &= (value == identity).all(axis=1)
        idx = np.flatnonzero(alive)
        print("twist=%-5s stage 1 survivors: %d" % (twist, len(idx)))

        for k in idx:
            d, dinv = D[k], Dinv[k]
            ok = True
            for _name, word in words:
                value = identity
                for factor, matrix in word:
                    key = matrix.tobytes()
                    letter = (iota[key] if factor == 1
                              else perm_mul(perm_mul(d, table[key]), dinv))
                    value = perm_mul(value, letter)
                if not np.array_equal(value, identity):
                    ok = False
                    break
            if ok:
                survivors.append((twist, D[k].tolist()))

    print("\nSCREEN (A) survivors:", len(survivors))
    if survivors:
        print("   FAILS -- example:", survivors[0])
        return 1
    print("   passes -- no degree-%d finite quotient kills the list" % m)
    return 0


if __name__ == "__main__":
    sys.exit(main())
