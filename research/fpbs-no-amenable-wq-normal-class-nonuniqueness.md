---
rg: 2
id: fpbs-no-amenable-wq-normal-class-nonuniqueness
kind: claim
title: Every Cayley graph of a nonamenable group without an infinite amenable wq-normal subgroup has strict thresholds
distinct_from:
  fpbs-amenable-wq-normal-class-nonuniqueness: that is the complementary class, groups having an infinite amenable wq-normal subgroup, where the gap is equivalent to relative subcriticality; this is every other nonamenable finitely generated group.
artifacts:
  - research/artifacts/fpbs/docs/relative-susceptibility-reduction.md
---

**OPEN.** Let `Gamma` be a nonamenable finitely generated group none of whose
infinite amenable subgroups is wq-normal. Then every Cayley graph of `Gamma` has
`p_c < p_u`.

This is the complement in the case split
`fpbs-bs-split-by-amenable-wq-normal-subgroup`. The split makes the reduction
for groups with an amenable wq-normal subgroup a genuine part of the goal's
decomposition, rather than a disconnected special case.

## Attempts

* **Deferred to the existing universal routes.** For these groups the
  relative-susceptibility reduction is unavailable by definition, and no
  class-specific mechanism is proposed here. Every live route into
  `fpbs-benjamini-schramm-universal` would settle this claim. That includes the
  acylindrically hyperbolic groups in the class, which `fpbs-sc-choi-seo`
  already covers. Where it stops: no attack uses the absence of amenable
  wq-normal subgroups as a hypothesis.
* **Remove what the cited theorems cover, and describe the rest.** The route
  `fpbs-no-amenable-wq-normal-via-cost-and-acylindricity` removes two kinds of
  group.
  - Groups not of fixed price one, by
    `fpbs-non-fixed-price-one-has-nonuniqueness`. By
    `fpbs-wq-normal-price-one-subgroup-forces-price-one`, every such group lies
    in this class.
  - Acylindrically hyperbolic groups, by `fpbs-sc-choi-seo`. This includes every
    group in the class that splits nondegenerately over an amenable subgroup
    (`fpbs-amenable-splittings-are-ah-or-amenable-wq-normal`).

  What remains is `fpbs-residual-price-one-non-ah-class-nonuniqueness`. It is
  nonempty: it contains `T x T'` for torsion Tarski monsters, and
  `B(m,n) x B(m',n')` for odd `n, n' >= 1003`
  (`fpbs-residual-class-has-torsion-products`). A single monster, or a
  centerless torsion-free Tarski monster, is a member exactly when it has fixed
  price one.

  **Where it stops:** the residual class has concrete members, and no cited
  percolation theorem applies to them. Their Cayley graphs are unimodular, so
  results for nonunimodular transitive graphs do not apply either. The
  hypothesis is used only structurally, through almost malnormal hulls and the
  exclusion of amenable splittings, never in a percolation estimate.
