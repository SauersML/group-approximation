---
rg: 2
id: iwahori-vertex-finite-image-capture
kind: claim
title: A vertex of an almost compatible Iwahori pair is close to a finite-image representation
distinct_from:
  iwahori-one-vertex-congruence-capture: that asks for proximity to congruence representations; this asks only for proximity to representations with finite image, of any kind. Congruence capture implies it, and it says nothing about non-congruence finite quotients.
  iwahori-finite-image-vertex-congruence-capture: that is the complementary half, which assumes the first vertex already has finite image; this is the half that must remove infinite-image mass.
  iwahori-bounded-dimensional-vertex-constituents-are-congruence: that proves the bounded-dimensional part of this and more, since it gives congruence rather than finite image; this is the statement for constituents of every dimension.
---

**OPEN.** Notation as in `iwahori-congruence-capture-transfers-across-one-edge`.
For an exact representation `alpha` of `C = SL_2(Z)` put

```text
A_fin(alpha) = inf { d_2(alpha, rho) : rho exact rep of C with finite image, any dimension }.
```

> **(FI)** For every sequence of exact pairs `pi_n` with `def(pi_n) -> 0`, we
> have `A_fin(pi_(n,+)) -> 0`.

**Role.** This is the *infinite-image half* of
`iwahori-one-vertex-congruence-capture`. By the route
`iwahori-capture-from-finite-image-and-finite-image-congruence`, capture is
equivalent to (FI) together with
`iwahori-finite-image-vertex-congruence-capture`. The Attempt of 2026-09-17
on the target names "almost `t`-transportability excludes positive-mass
infinite-image constituents" as the missing mechanism. (FI) is exactly that
mechanism, stated as a node of its own.

**What is already known.**
* **Bounded dimension.** By
  `iwahori-bounded-dimensional-vertex-constituents-are-congruence`, the
  constituents of dimension at most `D`, apart from normalized mass `o(1)`,
  are within `o(1)` of congruence on generators, so of finite image. A
  countersequence to (FI) must therefore carry its infinite-image mass on
  irreducible constituents whose dimensions tend to infinity.
* **The second vertex must be used.** The bounded-dimensional input above
  comes only from Peterson--Thom applied to `SL_2(Z[1/2])`. Nothing recorded
  in the graph approximates a general representation of `C` by
  finite-image ones in `d_2`. So a proof of (FI) should not be expected
  from `C` alone.
* **Failure mode that is excluded.** Every countersequence has growing-degree
  constituents. So no construction from a fixed small Lie-group
  representation, a triangle group, or a bounded-degree family can refute
  (FI).
