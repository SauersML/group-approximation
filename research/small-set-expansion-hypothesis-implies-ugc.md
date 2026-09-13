---
rg: 2
id: small-set-expansion-hypothesis-implies-ugc
kind: claim
title: The Gap-Small-Set Expansion Conjecture implies the Unique Games Conjecture (Raghavendra--Steurer 2010, Theorem 1.4)
distinct_from:
  small-set-expansion-hypothesis: that is the open hardness hypothesis; this is the proved implication from it to UGC.
  rich-2to1-conjecture-is-equivalent-to-ugc: that is the Braverman--Khot--Minzer equivalence with Rich 2-to-1 games; this is the Raghavendra--Steurer one-way implication from graph expansion.
---

**ESTABLISHED, BY CITATION.** If `small-set-expansion-hypothesis` holds, then
`unique-games-conjecture` holds. The reduction maps a graph `G` to a unique
game whose label-extended structure lives on tensor powers of `G` with noise.
Non-expanding sets of measure `delta` give almost-satisfying labelings, and
near-perfect expansion of small sets forces negligible value.

Raghavendra--Steurer--Tulsiani (arXiv:1011.2586), Corollary 3.3, sharpen this
to an equivalence. SSEH is equivalent to their Hypothesis 3.1, UGC on instances
whose constraint graph has `Phi(S) > 1 - eps` for every `S` with
`delta <= mu(S) <= M delta`. That equivalence is recorded in the citation route
but is not needed for the implication.

DERIVATION small-set-expansion-hypothesis-implies-ugc-citation
