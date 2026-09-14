---
rg: 2
id: two-generator-balanced-kervaire-failures-need-length-16
kind: claim
title: No two-generator balanced presentation of total relator length at most 15 carries a Kervaire killing failure, because each one with trivial abelianization is trivial, finite, or has a finite quotient of index at most 8
distinct_from:
  kervaire-killing-failure-over-deficiency-zero-group-exists: that is the OPEN existence claim for any balanced presentation; this certifies that its two-generator witnesses need total relator length above 15.
  deficiency-zero-kervaire-failure-forbids-finite-quotients: that is the necessary-condition filter; this applies it exhaustively to every short two-generator balanced presentation.
  short-balanced-trivial-presentations-are-trivial-or-ak3: that sorts balanced presentations of the trivial group up to Andrews--Curtis moves; this is about which groups short balanced presentations present, and asserts nothing about Andrews--Curtis equivalence.
artifacts:
  - research/artifacts/balanced-kervaire-search-2026-09-13.md
---

**ESTABLISHED** through `two-generator-balanced-kervaire-census-proof` (exhaustive
exact computation). Unreviewed. No novelty is claimed.

Let `G = <x, y | r_1, r_2>` with `|r_1| + |r_2| <= 15`. Up to free and cyclic
reduction, rotation and inversion of each relator, swapping the relators and the
eight signed permutations of `{x, y}`:

1. If `H_1(G) != 0`, `G` has a nontrivial finite quotient.
2. There are 24571 classes with `H_1(G) = 0`. Of these:
   - 24539 present the trivial group;
   - 24 present a perfect group of order 120;
   - 8 (total length 14 or 15) have a proper subgroup of index 7 or 8, hence a
     nontrivial finite quotient.

So no word `w in G * <t>` of exponent sum `+-1` kills a nontrivial such `G`: a
trivial `G` is not a witness, and every other class has a nontrivial finite
quotient, which item 3 of
`deficiency-zero-kervaire-failure-forbids-finite-quotients`
rules out.

**Consequence.** By `deficiency-zero-kervaire-failure-yields-whitehead-counterexample`,
a two-generator balanced witness for `kervaire-killing-failure-over-deficiency-zero-group-exists`,
and with it any two-generator balanced killing failure of that form, needs total
relator length at least 16.
