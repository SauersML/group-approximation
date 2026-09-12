---
rg: 2
id: leavitt-one-sided-pairs-are-unit-translates-of-s0-t0
kind: claim
title: Every one-sided inverse pair in the binary Leavitt algebra is a unit translate of the pair t_0 s_0 = 1
distinct_from:
  binary-leavitt-algebra-not-directly-finite: that exhibits one non-invertible one-sided pair; this proves every such pair is carried to that one by a single unit.
  binary-leavitt-algebra-is-purely-infinite-by-monomials: that is the monomial compression lemma for nonzero elements; this is the orbit theorem for one-sided inverse pairs that the lemma makes possible.
artifacts:
  - research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md
---

Let `R = L_(F_2)(1,2)` and `Q = R^x`. If `alpha, beta` in `R` satisfy
`beta alpha = 1 != alpha beta`, then there is `w` in `Q` with

    w alpha = s_0,        beta w^(-1) = t_0.

So the one-sided inverse pairs of `R` form one orbit under
`(alpha, beta) -> (w alpha, beta w^(-1))`.

The unit is explicit: `w = s_0 beta + y` and `w^(-1) = alpha t_0 + x`, where
`x y = 1 - alpha beta` and `y x = s_1 t_1` implement the equivalence of the two
defect idempotents. That equivalence exists because a defect idempotent
`p = 1 - alpha beta` satisfies `R ~= R (+) pR`, while the monomial lemma gives
`pR ~= pR (+) R`, so `pR ~= R`. Sections 2 and 3 of the artifact give the
proof.

Consumer: `leavitt-inverse-defects-are-visible-or-invisible`, which lifts this
orbit statement to the group algebra `F_2[Q]`.
