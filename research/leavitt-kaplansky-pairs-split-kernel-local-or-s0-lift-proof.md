---
rg: 2
id: leavitt-kaplansky-pairs-split-kernel-local-or-s0-lift-proof
kind: route
title: Classify left-invertible non-units of R as translates of s_0 and translate pairs by trivial units
target: leavitt-kaplansky-pairs-split-kernel-local-or-s0-lift
requires:
  - binary-leavitt-nonzero-projectives-are-free
  - leavitt-unit-group-algebra-surjects-onto-leavitt
artifacts:
  - research/artifacts/leavitt-kaplansky-pair-dichotomy-2026-09-12.md
---

Complete proof in the artifact, Lemmas 1 and 2 and the Theorem.

* Lemma 1: from `yx = 1 != xy`, the nonzero projective `(1-xy)R` is isomorphic to `R`, giving `z`
  and `w` with `wz = 1`, `zw = 1 - xy`, `yz = 0` and `wx = 0`. Then `u = x t_0 + z t_1` has
  inverse `s_0 y + s_1 w`, and `u s_0 = x`.
* Lemma 2: a left inverse of `s_0` is `t_0 + r t_1`, and the involution `1 + s_0 r t_1` fixes
  `s_0` on the left and turns it into `t_0` on the right.
* Theorem: translating `alpha` on the left and `beta` on the right by the same trivial units
  preserves `beta alpha = 1` and conjugates `alpha beta`.

The surjection supplies the ambient evaluation map; only its homomorphism property is used.
