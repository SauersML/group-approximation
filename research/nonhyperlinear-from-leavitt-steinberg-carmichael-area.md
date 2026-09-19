---
rg: 2
id: nonhyperlinear-from-leavitt-steinberg-carmichael-area
kind: route
title: Apply high-chromatic packing to the exact lifted Thompson packet in St20
target: non-hyperlinear-group
requires:
  - leavitt-steinberg-bounded-area-carmichael-lift
  - thompson-v-lifts-through-binary-leavitt-steinberg-cover
  - bounded-area-high-chromatic-conjugacy-collapse
---

Take `Delta=St_20(L_2(F_2))` and the nontrivial lifted three-cycle `b`.
For each `M`, use the common-pivot family from
`leavitt-steinberg-bounded-area-carmichael-lift` and the graph `K_M`.  Its
chromatic number is `M`, every vertex is a conjugate of `b`, and `(LSC1)` is
exactly the uniform cube/edge area hypothesis of the bounded-area
high-chromatic collapse theorem.  That theorem kills `b` in every
homomorphism from `Delta` to a tracial matrix ultraproduct.  The injective
Thompson lift gives `b!=1`, so a regular-character embedding is impossible.
