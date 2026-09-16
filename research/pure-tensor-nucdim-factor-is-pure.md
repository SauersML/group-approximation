---
rg: 2
id: pure-tensor-nucdim-factor-is-pure
kind: claim
title: A pure algebra tensored with a separable finite-nuclear-dimension algebra is pure
distinct_from:
  stw99-problem-xcv-pure-tensor-permanence: that asks for two arbitrary pure factors; this requires the second factor to be separable of finite nuclear dimension but does not require it to be pure (for example C([0,1])).
  pure-tensor-nucdim-no-pi-quotient-is-pure: that adds the hypothesis that no quotient of the product has a nonzero compact properly infinite Cuntz class.
artifacts:
  - research/artifacts/nucdim-factor-comparison-divisibility-2026-09-16.md
---

Let `A` be a pure C*-algebra and let `B` be a separable C*-algebra with finite
nuclear dimension.  Then `A tensor_min B` is pure.

This is a case of the question, recalled in the introduction of Seth--Vilalta
(arXiv:2602.14809v2), whether `B tensor_min A` is pure whenever `A` is pure.
Seth--Vilalta treat `B = C(X)` under the extra hypothesis that `A` is simple
or that no quotient of `A` has a nonzero compact properly infinite Cuntz class
(their Cor. 5.9 and Thm 5.11).  They also treat unital separable ASH `B` when
`A` is simple or residually stably finite (their Thm 6.7 and Rem. 6.8).  When
`B` is also pure the claim is a case of Problem XCV.

## Attempts

- `pure-tensor-nucdim-factor-pure-iff-global-glimm` reduces this claim to the
  Global Glimm Property of `A tensor_min B`
  (`pure-tensor-nucdim-factor-has-global-glimm`): comparison and bounded
  divisibility transfer from `A` through the order zero colours of `B`
  (`nucdim-factor-transfers-m-comparison`,
  `nucdim-factor-transfers-bounded-divisibility`), and the Seth--Vilalta
  dimension reduction turns them into purity once a two-piece splitting is
  available.
- `pure-tensor-nucdim-no-pi-quotient-is-pure` proves the claim when no quotient
  of `A tensor_min B` has a nonzero compact properly infinite Cuntz class.
- Direct shortcut that fails: Antoine--Perera--Thiel--Vilalta Theorem 6.5
  (Global Glimm plus finite nuclear dimension gives purity) cannot be applied,
  since `A tensor_min B` need not have finite nuclear dimension.
- Direct shortcut that fails: dividing colour by colour (Theorem B of the
  artifact) produces pieces whose images under different colours overlap, so
  the division constant `m+1` cannot be removed this way; no bound on the
  overlap was found.
