---
rg: 2
id: fpbs-amenable-wq-normal-class-nonuniqueness
kind: claim
title: Every Cayley graph of a nonamenable group with an infinite amenable wq-normal subgroup has strict thresholds
distinct_from:
  fpbs-fixed-price-one-percolation-kernel: that is the positive statement for all nonamenable fixed-price-one groups; this is the subclass with an infinite amenable wq-normal subgroup, where the threshold gap is exactly relative subcriticality along that subgroup.
  fpbs-product-every-generating-set: that is the direct-product class H x K with K arbitrary infinite; this class needs an amenable wq-normal subgroup, by fpbs-product-amenable-subgroup-wq-normal it contains every product one of whose factors has an infinite amenable subgroup (including F_2 x F_2), and also non-product examples such as braid groups and Seifert-fibred groups; it misses only products of torsion factors whose amenable subgroups are all finite.
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
`Z^d x| SL_d(Z)`, and non-solvable Baumslag--Solitar groups. It also contains
`F_2 x F_2` (Choi--Seo Question 1.7's barometer) and every product of infinite
groups with a non-torsion factor, because `{1} x <a>` is wq-normal there
(`fpbs-product-amenable-subgroup-wq-normal`). None of the examples listed here is
acylindrically hyperbolic, so `fpbs-sc-choi-seo` supplies none of them.

The live route is
`fpbs-amenable-wq-normal-class-via-relative-susceptibility`. Its only open
premise is `fpbs-amenable-wq-normal-relative-subcriticality`.

## Attempts

* **Reduce to relative subcriticality.** Done, by
  `fpbs-bs-iff-finite-relative-susceptibility`. The class claim is now
  equivalent to the premise, group by group. See that premise's `## Attempts`
  for the four direct attacks and where each stops.
