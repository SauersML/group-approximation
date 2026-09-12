---
rg: 2
id: surjunctivity-failure-descends-to-binary-alphabet
kind: claim
title: A group carrying a strict automaton over some finite alphabet carries one over two symbols
distinct_from:
  strict-rule-pairs-pass-to-product-alphabets: that moves strictness up along multiples of the alphabet size with the tables fixed; this asks for strictness to move down to two symbols, with the tables allowed to change.
artifacts:
  - research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md
---

**OPEN.** If a group `K` is not `A`-surjunctive for some finite alphabet `A`, then `K` is not
`{0,1}`-surjunctive. The memories and tables may change.

Together with `every-group-is-binary-surjunctive`, this would reduce Gottschalk's conjecture to
two symbols (`gottschalk-via-binary-alphabet-descent`).

## Attempts

- **Fixed tables, via products.** `strict-rule-pairs-pass-to-product-alphabets` moves strictness
  only from `k` to multiples `kl`, never down.
- **Fixed tables do not descend at all.** `equal-label-table-is-strict-at-three-symbols-not-two`
  shows that the table `x_a = x_b` with a discrete reverse table admits strict rules over every
  alphabet with at least three symbols and over none with two. Any group-level descent must
  therefore change the tables, e.g. by enlarging the memories.
- **Retraction onto a sub-alphabet.** Using `mu o r` and `nu o r` loses the fiber position of the
  demanded cell. When the class of `(1,1)` meets only relay `1`, that relay must carry both the
  code's symbol and the fiber position. So the extension fails unless the fibers have equal size,
  and equal fibers are exactly products. Artifact Section 5.
- **Erasure symbol.** The sink loses the values of relays reading a starred cell, and the forward
  identity uses every relay.
- **Block codes over a finite subgroup `H` with `2^|H| >= |A|`.**
  - Decoding `x -> (d((x(g h))_h))_g` is equivariant.
  - Encoding needs an equivariant choice of positions inside each coset `gH`, which a group does not
    supply without markers.
  - So an `A`-configuration cannot be written equivariantly in binary, and no binary strict
    automaton results.
- No literature source was checked for this statement.
- **Reformulation and the marker obstruction** (w3-alphabet). Descent is equivalent to an equivariant
  continuous binary coding with a one-sided inverse: an equivariant continuous injection
  `e : A^K -> {0,1}^K` with equivariant continuous retraction `r`, `r o e = id`, `e(A^K)` clopen; then
  `e o tau o r` (identity off the image) is a strict automaton on `{0,1}^K`. The only known binary coding
  is block coding over a finite subgroup `H <= K` with `2^{|H|} >= |A|`, whose encoding step needs an
  equivariant marking of `K/H` (an equivariant transversal), a coloring/SFT datum a group need not admit.
  On a finitely generated infinite simple group — the hosts the conjecture reduces to — there is no proper
  finite-index subgroup and no nontrivial finite quotient, and a finite `H` has infinite-index normalizer,
  so no equivariant marking of `K/H` exists and block-code descent is unavailable on exactly those hosts.
  Any descent proof for the target hosts must give a markerless equivariant binary coding; none is known.
  This marker argument is a structural sketch, not a formalized theorem. Artifact
  `research/artifacts/alphabet-ascent-and-binary-descent-2026-09-12.md`, Section 3.
