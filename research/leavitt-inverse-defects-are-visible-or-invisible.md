---
rg: 2
id: leavitt-inverse-defects-are-visible-or-invisible
kind: claim
title: A Kaplansky pair over the Leavitt unit group translates to a lift of (s_0, t_0) or to a pair in 1 + ker(pi)
distinct_from:
  leavitt-unit-group-algebra-not-directly-finite: that is the open existence of a one-sided inverse pair in F_2[R^x]; this is the established normalization of any such pair into one of two exact lifting problems, and asserts neither.
  left-invertible-lift-of-s0-in-leavitt-group-algebra: that is the open visible lifting problem; this proves that every failure with a visible defect is an instance of it, and names the second, invisible problem.
  direct-finiteness-not-inherited-by-quotients: that says the Leavitt surjection transports nothing by itself; this says exactly what a transported failure must look like over that surjection.
artifacts:
  - research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md
  - research/artifacts/gottschalk-negative-side-verification-2026-09-12.md
---

Let `R = L_(F_2)(1,2)`, `Q = R^x`, `S = F_2[Q]`, `pi : S ->> R` the evaluation,
`K = ker pi` and `K^+ = F_2 1 + K`. Let `b a = 1 != a b` in `S` and
`delta = 1 - ab`.

* **(V)** If `pi(delta) != 0`, there is `w` in `Q` such that `a' = [w] a` and
  `b' = b [w^(-1)]` satisfy `b' a' = 1 != a' b'`, `pi(a') = s_0` and
  `pi(b') = t_0`.
* **(I)** If `pi(delta) = 0`, then `r = pi(a)` is in `Q`, and `a' = [r^(-1)] a`,
  `b' = b [r]` satisfy `b' a' = 1 != a' b'`, `pi(a') = pi(b') = 1`, with defect
  in `K`.

Consequently `S` is not directly finite if and only if

* (V*) some lift of `s_0` is left invertible in `S` (and its left inverse can
  then be taken over `t_0`, through the involution `1 + s_0 (pi(b) s_1) t_1`),
  which is `left-invertible-lift-of-s0-in-leavitt-group-algebra`; or
* (I*) `K^+` is not directly finite, which is
  `leavitt-evaluation-kernel-unitization-not-directly-finite`.

Every other evaluation pattern of a witness is a translate by one group element.
Searches and proofs may fix either normal form. By
`leavitt-stable-finiteness-equals-direct-finiteness` the matrix versions reduce
to the same two problems.

Also proved (Proposition 6 of the artifact): in any group algebra `k[G]` over a
field, a defect `1 - ab` is never equivalent to `1`, since that would put a
unital binary Leavitt family in `k[G]`. In case (V) the defect lifts `s_1 t_1`,
which is equivalent to `1` in `R`. So a witness to (V*) lifts the pair
`(s_0, t_0)` exactly but cannot be completed to a lift of the whole family.
