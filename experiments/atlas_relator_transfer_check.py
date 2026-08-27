"""Check the commutator transfer identity of the completeness derivation.

`notes/ATLAS_COMPLETENESS_DERIVATION_2026-08-15.md` Lemma 3.1 claims

    [[X, Y], Z] = [X, [Y, Z]]

for X, Y, Z carrying roots (i,l), (l,k), (k,j) with i, j, k, l distinct, given
the stated (St2) instances and the centrality of T = [X, V].

The lemma is a statement about the PRESENTED group `G_0`, so evaluating in `Q`
cannot prove it.  What evaluation in `Q` does do is catch an algebra slip in
the four-conjugation computation: if the identity as written were wrong (wrong
commutator convention, an inverted conjugation, a mis-ordered product), it
would already fail in `Q`, where all the hypotheses hold.  It also confirms
that both sides equal the expected `x_ij(a b)`, i.e. that the two spare-index
definitions agree in `Q` -- which is what makes them candidates to be equal in
`G_0`.

This is a necessary-condition check, and is labelled as such.
"""

import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from atlas_kernel_collision_enumerator import evaluate_word  # noqa: E402
from atlas_relator_rank5_dictionary import (  # noqa: E402
    COEFF_LETTERS,
    leavitt_equal,
    rank5_word,
)
from atlas_relator_rank5_full_family import (  # noqa: E402
    rank5_word_multi,
    target_multi,
)
from atlas_two_chart_search import commutator, reduce_word  # noqa: E402


def main():
    memo = {}

    def x(i, j, b):
        return rank5_word(i, j, b, memo)[0]

    checked = 0
    transfer_ok = 0
    spare_ok = 0
    for i, j, k, l in itertools.permutations(range(1, 6), 4):
        for a, b in itertools.product(COEFF_LETTERS, repeat=2):
            X = x(i, l, a)          # root (i,l)
            Y = x(l, k, "1")        # root (l,k)
            Z = x(k, j, b)          # root (k,j)

            lhs = reduce_word(commutator(commutator(X, Y), Z))
            rhs = reduce_word(commutator(X, commutator(Y, Z)))

            lv, rv = evaluate_word(lhs), evaluate_word(rhs)
            if leavitt_equal(lv, rv):
                transfer_ok += 1
            else:
                print("TRANSFER FAILS at", (i, j, k, l, a, b))
                return 1

            # both sides should be x_ij(ab)
            if leavitt_equal(lv, target_multi(i, j, [a, b])):
                spare_ok += 1
            else:
                print("VALUE MISMATCH at", (i, j, k, l, a, b))
                return 1
            checked += 1

    print("index quadruples x coefficient pairs checked:", checked)
    print("  [[X,Y],Z] = [X,[Y,Z]] in Q:", transfer_ok)
    print("  both sides equal x_ij(ab) in Q:", spare_ok)

    # the two spare-index definitions, directly
    agree = 0
    for i, j in itertools.permutations(range(1, 6), 2):
        spares = [s for s in range(1, 6) if s not in (i, j)]
        for a, b in itertools.product(COEFF_LETTERS, repeat=2):
            values = []
            for s in spares:
                word = reduce_word(commutator(x(i, s, a), x(s, j, b)))
                values.append(evaluate_word(word))
            if all(leavitt_equal(values[0], v) for v in values[1:]):
                agree += 1
            else:
                print("SPARE MISMATCH at", (i, j, a, b))
                return 1
    print("roots x coefficient pairs with all three spare chains agreeing "
          "in Q:", agree)

    # canonical dictionary word agrees with every spare chain
    canon_ok = 0
    for i, j in itertools.permutations(range(1, 6), 2):
        spares = [s for s in range(1, 6) if s not in (i, j)]
        for a, b in itertools.product(COEFF_LETTERS, repeat=2):
            canon = evaluate_word(rank5_word_multi(i, j, [a, b], memo))
            for s in spares:
                word = reduce_word(commutator(x(i, s, a), x(s, j, b)))
                if not leavitt_equal(canon, evaluate_word(word)):
                    print("CANONICAL MISMATCH at", (i, j, a, b, s))
                    return 1
            canon_ok += 1
    print("roots x pairs where the canonical word matches every spare chain:",
          canon_ok)
    print()
    print("NOTE: these are necessary conditions in Q, not proofs in G_0.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
