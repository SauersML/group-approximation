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
* **Import Choi–Seo's nested-barrier theorem (Theorem 2.17) to the class
  (wave 20, host-geometry).** Dead for a large subclass, by
  `fpbs-cs-barrier-hypothesis-fails-finite-free-capacity-normal`.

  The invariant is the free-subset capacity `b(Kt)` of the cosets of a normal
  subgroup `K`. It is the largest finite `Y ⊆ Kt` such that distinct
  equal-length sequences from `Y` have distinct products. Roughly-branching
  witnesses meet `Kt` in at most `b(Kt)` points.

  The method dies at the magic-lemma step for every `K` with an infinite
  finitely generated subgroup and `b(Kt) < ∞` for all `t`. There, windows
  `A ⊆ K_0` avoid every `H ∈ H_D` and every `G_(D,E)`. This covers:
  - every infinite finitely generated virtually nilpotent normal `K`, via
    `b(Kt) <= L_t^d`, including `Z^2 x| F_2` and `Z^2 x| SL(2,Z)`;
  - every `H x K` with `K` free of free subsemigroups, via `b = 1`.

  The capacity is not always 1. `Z^2 x|_[[2,1],[1,1]] Z` has `b = 2`, so the
  wave-19 cyclic core lemma does not extend, and only the count does.

  Still open for this method: normal `K` containing a free subsemigroup
  (`F_2 x F_2`, `F_2 x BS(1,2)`), where `b = ∞`, and locally finite normal
  subgroups.
