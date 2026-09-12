---
rg: 2
id: fpbs-amenable-wq-normal-class-nonuniqueness
kind: claim
title: Every Cayley graph of a nonamenable group with an infinite amenable wq-normal subgroup has strict thresholds
distinct_from:
  fpbs-fixed-price-one-percolation-kernel: that is the positive statement for all nonamenable fixed-price-one groups; this is the subclass with an infinite amenable wq-normal subgroup, where the threshold gap is exactly relative subcriticality along that subgroup.
  fpbs-product-every-generating-set: that is the direct-product class H x K with K arbitrary infinite; this class needs an amenable wq-normal subgroup, so it contains products with an amenable factor and also non-split examples such as braid groups and Seifert-fibred groups, but not F_2 x F_2.
artifacts:
  - research/artifacts/fpbs/docs/relative-susceptibility-reduction.md
---

**OPEN.** Let `Gamma` be a nonamenable finitely generated group with an
infinite amenable wq-normal subgroup. Then every Cayley graph of `Gamma` has
`p_c < p_u`.

This is the class-level half of the case split
`fpbs-bs-split-by-amenable-wq-normal-subgroup`. It contains groups with infinite
center (braid groups `B_n` for `n >= 3`, spherical Artin groups, `Gamma x Z^k`),
Seifert-fibred 3-manifold groups with hyperbolic base (Choi--Seo Question 1.6),
`F_2 x Z` (Choi--Seo Question 1.3), lamplighters over nonamenable groups,
`Z^d x| SL_d(Z)`, and non-solvable Baumslag--Solitar groups. Since the normal
cases are never acylindrically hyperbolic, `fpbs-sc-choi-seo` supplies none of
them.

The live route is
`fpbs-amenable-wq-normal-class-via-relative-susceptibility`. Its only open
premise is `fpbs-amenable-wq-normal-relative-subcriticality`.

## Attempts

* **Reduce to relative subcriticality.** Done, by
  `fpbs-bs-iff-finite-relative-susceptibility`. The class claim is now
  equivalent to the premise, group by group. See that premise's `## Attempts`
  for the four direct attacks and where each stops.
