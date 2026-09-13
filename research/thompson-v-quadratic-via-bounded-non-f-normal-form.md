---
rg: 2
id: thompson-v-quadratic-via-bounded-non-f-normal-form
kind: route
title: "Dead: quadratic Dehn function for V by copying Migliorini's T normal form with boundedly many non-F letters"
target: thompson-v-has-quadratic-dehn-function
requires: []
---

**Dead approach, recorded so it is not retried.** It is killed by the
established obstruction
`thompson-v-elements-need-unboundedly-many-non-f-letters`, which invalidates
this route.

The approach: transfer Migliorini's proof that T has quadratic Dehn function
(arXiv:2410.23088) to V. For T, Proposition 4.2 writes every `f ∈ T \ F` as
`u(S_F) · C_0 · v(S_F)` with `|w| ≤ C‖f‖_T`, and Proposition 4.3 (the triangle
criterion) then reduces quadratic area to triangles of such normal forms,
settled with Guba's quadratic bound for F.

Why it dies: the order-break count `br` is subadditive, `br(F) = 1`, and the
depth-`k` block reversal has `br = 2^k`. So elements of V need a number of non-F
letters growing linearly in `br`, and no normal form for V with a bounded number
of non-F letters exists.

What survives: Proposition 4.3 itself. A proof for V through it needs normal
forms whose non-F part grows with the element, for instance permutation layers
controlled by `br`; see `thompson-v-has-quadratic-dehn-function`.
