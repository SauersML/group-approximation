---
rg: 2
id: padding-line-hardness-from-hadamard-gadget
kind: route
title: A Had_k gadget with s/c > 2 gives, via HHM+15 Corollary 2.26 and the equation-variable double cover, an NP-hard 2-label unique-games gap below the padding line
target: unique-games-np-hard-below-the-padding-line
requires: [hadamard-gadget-crosses-padding-line]
---

This route gives a sufficient condition. The conditional steps are short and
use HHM+15 Corollary 2.26, which is quoted in
`hadamard-gadget-deletion-ratio-window-proof`. The proof of Corollary 2.26 is
repaired there in item 6, because the Proposition 2.25 step it cites is
false as stated.

## Step 1: a rational gadget

Let a `(c, s)`-gadget for `Had_k` have `s/c > 2`. By item 1 of
`hadamard-gadget-deletion-ratio-window`, `R*(k) = K z*(P) > 2`, attained by a
balanced gadget `mu~` with `c = 1/K` and `s = z*(P)`.

* `z*(P)` is the value of a finite linear program with rational data.
* The optimal `mu` may be taken at a vertex, so it is rational. Its
  translation average `mu~` is then rational too.

So a witness can be taken with rational weights and rational `(c, s)` with
`s > 2c`.

## Step 2: 2-Lin(2) hardness

Choose a rational `eps > 0` with `s - eps > 2(c + eps)`, for example
`eps = (s - 2c)/4`. Put `c' = c + eps` and `s' = s - eps`, so `s' > 2c'`.

Corollary 2.26 then applies: given a Max-2-Lin(2) instance `I`, it is
NP-hard to tell `uval(I) <= c'` from `uval(I) >= s'`.

* In Proposition 2.17, the instance `I'` is Chan's instance with a scaled
  copy of the rational gadget on each constraint.
* Its weights are rational, and can be made positive integers by clearing
  denominators. This does not change `uval`.

## Step 3: the equation-variable double cover

From `I`, with equations `e: x_u x_v = b_e` of weight `w_e`, build a
bipartite unique game `U` with `K = 2`.

* **Vertices.** The left vertices are the equations and the right vertices
  are the variables.
* **Edges.** Each equation `e` has two edges of weight `w_e`: to `u` with the
  identity permutation, and to `v` with the permutation "multiply by `b_e`".
* **Values match.** Fix the right labels `x`.
  * If `x` satisfies `e`, the left label `x_u` satisfies both edges at `e`.
  * Otherwise every left label satisfies exactly one of the two.
  * So `val(U) = 1 - uval_x(I)/2` after optimizing, and
    `val(U) = 1 - uval(I)/2`.

This gives NP-hardness of `Gap-UG_2[1 - c'/2, 1 - s'/2]`.

* Both endpoints are rational, with `0 <= 1 - s'/2 < 1 - c'/2 < 1`.
* The deficit ratio is `(s'/2)/(c'/2) = s'/c' > 2`.
* Equivalently, `1 - s'/2 < 2(1 - c'/2) - 1`: the point is strictly below
  the padding line, as `unique-games-np-hard-below-the-padding-line` asks.

## Status

The route is conditional on `hadamard-gadget-crosses-padding-line`, which is
OPEN. By `hadamard-gadget-deletion-ratio-window` it can only be met with
`k >= 6`, with a true-soundness analysis, and with ratio below `5/2`.
