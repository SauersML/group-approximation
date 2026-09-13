---
rg: 2
id: bounded-removal-detection-from-detection-alone
kind: route
title: Purity and local expansion hold for every bounded removal, so detection alone gives bounded-removal detection
target: random-complex-bounded-removal-detected-by-quotient
requires: [random-complex-removed-perimeter-survives-in-finite-quotient, random-complex-bounded-removals-stay-local-expanders]
---

## Why sufficient

Fix `0 < η < 1/2`, let `t` be the integer from
`random-complex-removed-perimeter-survives-in-finite-quotient`, put
`p = n^(-1+η)` and sample `Y ~ Y(n,p)`. Two events hold a.a.s., so their
intersection does.

1. **Detection.** There are `T ⊂ Y(2)` with `|T| <= t` and `Δ ∈ T` such that the
   perimeter of `Δ` survives in a finite quotient of `π_1(Y \ T)`.
2. **Uniform structure.** By `random-complex-bounded-removals-stay-local-expanders`,
   for this `t`, every `T' ⊂ Y(2)` with `|T'| <= t` leaves `Y \ T'` pure and
   connected with 1-skeleton `K_n`, and `Y \ T'` is a `1/4`-local spectral expander.

On the intersection, the `T` from event 1 satisfies conditions 1–3 of
`random-complex-bounded-removal-detected-by-quotient`. The conditions of event 2
hold for every bounded removal, so the witness needs no extra choice.
