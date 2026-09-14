---
rg: 2
id: fpbs-product-amenable-subgroup-wq-normal
kind: claim
title: An infinite amenable subgroup of one factor is wq-normal in a product with an infinite second factor
distinct_from:
  fpbs-product-no-amenable-wq-normal: that is the open product case with no infinite amenable wq-normal subgroup; this lemma shows that case contains no product having an infinite amenable subgroup in either factor, so F_2 x F_2 and products of nonelementary hyperbolic groups lie in the other case.
  fpbs-hp-wq-normal-uniqueness-transfer: that imports the percolation consequence of wq-normality; this is a purely group-theoretic membership lemma for direct products.
artifacts:
  - research/artifacts/fpbs/docs/relative-susceptibility-reduction.md
---

**ESTABLISHED.** Let `H` and `K` be groups with `H` infinite, and let `A <= K`
be an infinite amenable subgroup. Then `B = {1} x A` is an infinite amenable
wq-normal subgroup of `G = H x K`.

Consequently every direct product of two infinite groups in which some factor
contains an infinite amenable subgroup lies in the class of
`fpbs-amenable-wq-normal-class-nonuniqueness`. Every finitely generated infinite
group that is not a torsion group contains `Z`, so this covers `F_2 x F_2`,
`F_2 x Z`, and every product of nonelementary hyperbolic groups. For all of them
`p_c < p_u` on a given Cayley graph is equivalent, by
`fpbs-bs-iff-finite-relative-susceptibility`, to finite expected intersection
of slightly supercritical clusters with `{1} x <a>` for an infinite-order `a`.

What remains outside the amenable wq-normal class among products are pairs of
infinite torsion groups all of whose amenable subgroups are finite, such as
products of Tarski monsters.

DERIVATION
fpbs-product-amenable-subgroup-wq-normal-proof
