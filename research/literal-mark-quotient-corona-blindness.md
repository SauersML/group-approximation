---
rg: 2
id: literal-mark-quotient-corona-blindness
kind: claim
title: Corona trace-invisibility in the literal marked quotient is exactly the finite residual
distinct_from:
  corona-hs-radical-is-finite-residual: Same theorem for the commuting-lamp quotient, where the invisible set is a locally finite elementary abelian group; here it is the level-collapse kernel of a free product and contains infinite-order elements.
  literal-mark-quotient-finite-residual: That claim is about homomorphisms to finite groups; this one is about all corona representations, and the content is that the two answers coincide.
  literal-mark-quotient-sofic: That claim gives permutation microstates in the Hamming metric; this one says every operator-norm corona model is trace-blind on a specific subgroup, which is a statement about a different mode of approximation.
  literal-mark-quotient-mf: That open claim asks for an operator-norm faithful corona model; this proved claim says every corona model is trace-blind on a specific subgroup, which constrains such a model without producing or excluding one.
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

For every corona representation `Theta` of `E/<w>`, the induced tracial
representation into the tracial ultraproduct kills the level-collapse kernel
`R`; and every element outside `R` is detected in normalized
Hilbert--Schmidt norm by some corona representation.  Hence the corona
Hilbert--Schmidt radical of `E/<w>` equals its finite residual `R`.

Consequently `Rad_MF(E/<w>)` is a normal subgroup of `R`, and a faithful MF
model of `E/<w>` must separate elements of `R` on corners of vanishing
normalized rank.  The same statement with the same proof holds for
`W/<zeta>` (`corona-hs-radical-is-finite-residual`), so both open
quotient-MF claims have the same shape: separate a trace-invisible level
collapse in operator norm.
