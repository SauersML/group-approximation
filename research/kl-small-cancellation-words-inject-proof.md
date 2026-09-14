---
rg: 2
id: kl-small-cancellation-words-inject-proof
kind: route
title: Count free-product pieces and apply the relative Greendlinger lemma
target: kl-small-cancellation-words-inject-every-coefficient-group
requires: [greendlinger-free-product-lemma]
---

Let `R` be the symmetrized closure of `w` over `F = G * <t>`: all weakly
cyclically reduced conjugates of `w` and `w^(-1)` (Lyndon--Schupp V.9).  Every
element of `R` has length `2k`.

**Pieces.**  A piece is a common prefix `b` of distinct `r_1, r_2 in R` with
`r_1 = b c_1` and `r_2 = b c_2` semi-reduced.  Semi-reduction lets the last
syllable of `b` merge with the first syllable of `c_i`, so the final syllable
of `b` may be a proper part of the corresponding syllable of `r_i`.
Conjugation by a factor element changes the first syllable of a cyclic
conjugate arbitrarily, so the first syllable of `b` is unconstrained as well.
Every interior syllable of `b` is followed inside `b` by a syllable from the
other factor, so it must equal the corresponding syllable of `r_1` and of
`r_2` exactly.  The interior of `b` is therefore a block of `|b| - 2`
syllables occurring exactly at two positions of the cyclic words `w^(+-1)`.
The positions are different because `r_1 != r_2` and `w` is not a proper
power.  Hence `|b| <= sigma(w) + 2`.

The bound is sharp in general.  Pieces `x t^f y` of length three exist as
soon as two exponents agree (`e_i = e_j`) or are opposite (`e_i = -e_j`),
with `x, y` chosen freely.  They need no coincidence among the coefficients.

**Small cancellation.**  Under (SC1), `|b| < k/3 = |r|/6` for every piece, so
`R` satisfies `C'(1/6)` over the free product; also `|r| = 2k > 6`, since
(SC1) forces `k > 6`.  By `greendlinger-free-product-lemma` (Lyndon--Schupp
Theorem V.9.3), a nontrivial reduced element of `<<R>>` contains more than
`|r|/2 = k` consecutive syllables of some `r in R`.  A nontrivial `g in G` has
free-product length one, so it does not lie in `<<w>>`.
