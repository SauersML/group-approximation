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
