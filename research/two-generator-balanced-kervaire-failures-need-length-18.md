---
rg: 2
id: two-generator-balanced-kervaire-failures-need-length-18
kind: claim
title: No two-generator balanced presentation of total relator length at most 17 carries a Kervaire killing failure, because each one with trivial abelianization is trivial or has a verified finite quotient
distinct_from:
  two-generator-balanced-kervaire-failures-need-length-16: that certifies total relator length at most 15; this extends the exhaustive certificate to total lengths 16 and 17.
  kervaire-killing-failure-over-deficiency-zero-group-exists: that is the OPEN existence claim for any balanced presentation; this certifies that its two-generator witnesses need total relator length above 17.
  deficiency-zero-kervaire-failure-forbids-finite-quotients: that is the necessary-condition filter; this applies it exhaustively to every two-generator balanced presentation of total length at most 17.
artifacts:
  - research/artifacts/balanced-kervaire-census-16-2026-09-14.md
  - research/artifacts/balanced-kervaire-search-2026-09-13.md
---

**ESTABLISHED** through `two-generator-balanced-kervaire-census-to-length-17-proof` (exhaustive
exact computation with independent checks). Unreviewed. No novelty is claimed.

Let `G = <x, y | r_1, r_2>` with `|r_1| + |r_2| <= 17`. Classes are taken up to free and cyclic
reduction, rotation and inversion of each relator, swapping the relators and the eight signed
permutations of `{x, y}`.

1. If `H_1(G) != 0`, `G` has a nontrivial finite quotient.
2. There are 181842 classes with `H_1(G) = 0`: 24571 of total length at most 15 (see
   `two-generator-balanced-kervaire-failures-need-length-16`), 29929 of total length 16 and
   127342 of total length 17. Of the 157271 classes of total length 16 or 17:
   - 157076 present the trivial group;
   - 175 present a nontrivial finite perfect group: 168 of order 120, 6 of order 336, and one of
     order 5322240, namely `<x, y | x^-2 y^-1 x^-1 y^-1 x^2 y, x^-1 y^-4 x^-1 y x^-1 y>`
     (class 137426);
   - 20 have a proper subgroup of index 7 or 8, hence a nontrivial finite quotient.

So no word `w in G * <t>` of exponent sum `+-1` kills a nontrivial such `G`. A trivial `G` is not
a witness, and every other class has a nontrivial finite quotient, which item 3 of
`deficiency-zero-kervaire-failure-forbids-finite-quotients` rules out.

**Consequence.** By `deficiency-zero-kervaire-failure-yields-whitehead-counterexample`, a
two-generator balanced witness for `kervaire-killing-failure-over-deficiency-zero-group-exists`,
and with it any two-generator balanced killing failure of that form, needs total relator length at
least 18.
