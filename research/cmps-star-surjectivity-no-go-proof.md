---
rg: 2
id: cmps-star-surjectivity-no-go-proof
kind: route
title: Push CMPS copied-clause star-surjectivity through the contextwise R-star lift
target: star-surjective-nonaffine-context-blocks-fano-empty-link-lift
requires:
  - cmps-lemma20-is-radius-two-incidence-commutation
  - culf-mastel-rstar-fixed-language-gap-is-published
  - fano-cap-range-sections-cannot-encode-nonaffine-relations
  - rstar-fano-ghost-affine-hull-criterion
---

Read the incidence construction in CMPS Lemma 20, lines 427--436 of
arXiv:2510.03477v3.  A copied proper 3SAT clause is nonaffine, but every one
of its seven satisfying assignments extends through its complete constraint
star by copying the local values to the corresponding globals.  Apply the
contextwise witness maps of Culf--Mastel Corollary 6.7.  Their private
auxiliaries preserve consistency between neighboring gadgets; subdivision
only exposes satisfied conjuncts; and Proposition 6.2 extends every empty
endpoint pair.  Hence every tuple in every occurrence range of the copied
clause has a nonempty target-neighborhood link.

If the target nonempty-link sets were Fano caps, all occurrence ranges of a
section of the seven-point clause relation would be caps.  The established
cap-range theorem would make the clause relation affine, contradiction.

