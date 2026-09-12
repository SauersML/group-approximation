---
rg: 2
id: leavitt-kaplansky-pairs-split-kernel-local-or-s0-lift
kind: claim
title: Every one-sided inverse pair in F_2[R^x] is a group translate of a pair over 1 or of lifts of s_0 and t_0
distinct_from:
  leavitt-unit-group-algebra-not-directly-finite: that is the open existence of a strict pair; this is an established classification of all pairs, strict or not, into two kinds, and it exhibits none.
  left-invertible-lift-of-s0-in-leavitt-group-algebra: that is the open lift of s_0 with a left inverse; this proves that lift is exactly the visible-defect half of the headline, so pinning the value to s_0 loses nothing among visible defects.
  leavitt-kernel-unitization-not-directly-finite: that is the open kernel-local half; this is the classification that isolates it.
  binary-leavitt-nonzero-projectives-are-free: that is the imported projective-module input; this uses it to classify left-invertible non-units of R and then transports the classification to the group algebra.
artifacts:
  - research/artifacts/leavitt-kaplansky-pair-dichotomy-2026-09-12.md
---

Let `R = L_(F_2)(1,2)`, `G = R^x`, `A = F_2[G]`, `pi : A -> R` the evaluation map, and
`K = ker(pi)`. Let `alpha, beta` in `A` with `beta alpha = 1`.

1. If `pi(alpha)` is a unit `x`, then `[x^-1] alpha` and `beta [x]` lie in `1 + K`, still
   satisfy `beta' alpha' = 1`, and have reverse product conjugate to `alpha beta`.
2. If `pi(alpha)` is not a unit, there are `u, v` in `G` such that `alpha' = [v][u^-1] alpha`
   and `beta' = beta [u][v]` satisfy `pi(alpha') = s_0`, `pi(beta') = t_0` and
   `beta' alpha' = 1`. The pair is then strict automatically.

Consequently `A` is not directly finite exactly when either
* (i') some `k, l` in `K` satisfy `(1+l)(1+k) = 1 != (1+k)(1+l)`
  (`leavitt-kernel-unitization-not-directly-finite`), or
* (ii') some lifts of `s_0` and `t_0` multiply to `1` in that order
  (`left-invertible-lift-of-s0-in-leavitt-group-algebra`).

The two cases are told apart by whether the defect idempotent `1 - alpha beta` lies in `K`.

The engine is Lemma 1 of the artifact: every left-invertible non-unit of `R` equals `u s_0`, with
`u = x t_0 + z t_1` explicit once the complement `(1 - xy)R` is identified with `R`
(`binary-leavitt-nonzero-projectives-are-free`). Lemma 2 then normalizes the left inverse
`t_0 + r t_1` to `t_0` with the involution `1 + s_0 r t_1`.
