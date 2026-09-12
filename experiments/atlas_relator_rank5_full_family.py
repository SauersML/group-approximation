"""The FULL (St1)-(St3) instantiation at rank five, in atlas words.

The earlier family (`atlas_relator_rank5_relations.py`) mirrors the repo's
rank-three `relation_family()`.  Audited against the Steinberg presentation as
transcribed in `research/artifacts/atlas-relator-extraction-2026-08-15.md`,

    (St1)  E_ij(r) E_ij(s) = E_ij(r+s)
    (St2)  [E_ij(r), E_kl(s)] = 1                if i != l and k != j
    (St3)  [E_ij(r), E_jk(s)] = E_ik(rs)         if i != k

that family is a strict SUBSET of the instantiation on the ring generators:

  * (St2) was emitted for only 3 of the 25 coefficient pairs;
  * (St2) with `(k,l) = (i,j)` -- i.e. commutativity of the root subgroup,
    `[x_ij(a), x_ij(b)] = 1` -- was omitted entirely (the enumeration used
    unordered pairs of DISTINCT roots);
  * (St3) was emitted only where the product `rs` lands back in
    `{1,e,f,e^*,f^*} cup {0}`, i.e. for about ten of the 25 pairs.

This script emits the full instantiation.  (St1) contributes no relator on the
generating set, since `r+s` is not itself a generator: `x_ij(r+s)` is *defined*
as the product, and the content of additivity is consistency of that
definition, which is what the ring relations inside (St3) carry.

For (St3) the right-hand side `x_ik(rs)` is needed for a product of two
letters, so the dictionary is extended to accept a whole factor list.  Every
emitted word is verified exactly to lie in `Rbar`.
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
    ONE,
    PARENT,
    STAR_OF,
    SUFFIX,
    leaf,
    leavitt_equal,
    path,
    rank5_word,
    root_word,
    transvection_lengths,
)
from atlas_two_chart_search import (  # noqa: E402
    I4,
    commutator,
    inverse,
    leavitt_add,
    leavitt_is_one,
    leavitt_mul,
    product,
    reduce_word,
)

LETTER_ELEMENT = {
    "1": {((), ()): 1},
    "e": {((0,), ()): 1},
    "f": {((1,), ()): 1},
    "E": {((), (0,)): 1},
    "F": {((), (1,)): 1},
}


def product_element(factors):
    value = {((), ()): 1}
    for a in factors:
        value = leavitt_mul(value, LETTER_ELEMENT[a])
    return value


def target_multi(k, l, factors):
    """The exact Leavitt element 1 + E_k (prod factors) E_l^*."""
    left = {(path(leaf(k)), ()): 1}
    right = {((), path(leaf(l))): 1}
    body = leavitt_mul(leavitt_mul(left, product_element(factors)), right)
    return leavitt_add(ONE, body)


def coefficient_factors_multi(k, l, factors):
    out = []
    if SUFFIX[k] is not None:
        out.append(SUFFIX[k])
    out.extend(a for a in factors if a != "1")
    if SUFFIX[l] is not None:
        out.append(STAR_OF[SUFFIX[l]])
    return out or ["1"]


def rank5_word_multi(k, l, factors, memo):
    """An X-word for x_kl(prod factors), for a list of coefficient letters."""
    i, j = PARENT[k], PARENT[l]
    if i != j:
        return root_word(i, j, coefficient_factors_multi(k, l, factors), memo)
    left = rank5_word_multi(k, 5, factors, memo)
    right = rank5_word_multi(5, l, ["1"], memo)
    return reduce_word(commutator(left, right))


def generate_relators(verify=True):
    """Return the distinct full-family relators in deterministic order.

    ``verify=False`` skips the exact Leavitt-kernel audit but does not change
    generation or deduplication.  It is used by the packet exporter, whose
    source families have already been independently verified by this script.
    """
    lengths = transvection_lengths()
    memo = {}
    single = {}

    def x(k, l, b):
        if (k, l, b) not in single:
            single[(k, l, b)] = rank5_word(k, l, b, memo)[0]
        return single[(k, l, b)]

    # -- extend and re-verify the dictionary on two-letter coefficients
    if verify:
        for k, l in itertools.permutations(range(1, 6), 2):
            for r, s in itertools.product(COEFF_LETTERS, repeat=2):
                word = rank5_word_multi(k, l, [r, s], memo)
                assert leavitt_equal(
                    evaluate_word(word), target_multi(k, l, [r, s])
                ), (k, l, r, s)

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

    # (St2) with (k,l) = (i,j): the root subgroup is abelian
    for i, j in itertools.permutations(range(1, 6), 2):
        for r, s in itertools.combinations(COEFF_LETTERS, 2):
            add("root_%d%d_%s%s" % (i, j, r, s),
                commutator(x(i, j, r), x(i, j, s)))
    n_root = len(words)

    # (St2) for distinct roots with i != l and k != j
    roots = [(i, j) for i in range(1, 6) for j in range(1, 6) if i != j]
    for (i, j), (k, ell) in itertools.combinations(roots, 2):
        if i != ell and k != j:
            for r, s in itertools.product(COEFF_LETTERS, repeat=2):
                add("orth_%d%d_%d%d_%s%s" % (i, j, k, ell, r, s),
                    commutator(x(i, j, r), x(k, ell, s)))
    n_orth = len(words) - n_root
    # NB: this block enumerates ALL pairs of distinct roots meeting the (St2)
    # side condition -- index-disjoint, same-source ((i,j),(i,l)) and
    # same-target ((i,j),(k,j)) alike.  The same-target instances are load
    # bearing: the spare-index derivation's [Z,V] = 1 hypothesis is one.

    # (St3) for every coefficient pair
    for i, j, k in itertools.permutations(range(1, 6), 3):
        for r, s in itertools.product(COEFF_LETTERS, repeat=2):
            rhs = rank5_word_multi(i, k, [r, s], memo)
            add("st3_%d%d%d_%s%s" % (i, j, k, r, s),
                product(commutator(x(i, j, r), x(j, k, s)), inverse(rhs)))
    n_st3 = len(words) - n_root - n_orth
    return list(zip(names, words)), lengths, (n_root, n_orth, n_st3)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--emit", default="")
    args = parser.parse_args()

    relators, lengths, counts = generate_relators(verify=True)
    names = [name for name, _word in relators]
    words = [word for _name, word in relators]
    n_root, n_orth, n_st3 = counts

    print("two-letter dictionary entries verified exactly:",
          20 * len(COEFF_LETTERS) ** 2)
    print("(St2) root-subgroup commutativity:", n_root)
    print("(St2) cross-root commutation (disjoint + same-source + "
          "same-target):", n_orth)
    print("(St3) Steinberg products:", n_st3)
    print("distinct nonidentity relators:", len(words))

    bad, boundary = [], 0
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
    print("CONSISTENCY %s" % ("OK" if boundary else "FAILURE"))

    if args.emit:
        with open(args.emit, "w") as handle:
            json.dump({"relators": [
                {"name": n, "syllables": len(w),
                 "x_length": sum(lengths[m.tobytes()] for _f, m in w),
                 "word": [[int(f), "".join(str(int(v)) for v in m.reshape(-1))]
                          for f, m in w]}
                for n, w in zip(names, words)]}, handle)
        print("wrote", args.emit)
    return 0


if __name__ == "__main__":
    sys.exit(main())
