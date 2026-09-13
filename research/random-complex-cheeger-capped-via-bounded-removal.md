---
rg: 2
id: random-complex-cheeger-capped-via-bounded-removal
kind: route
title: Detection after a bounded removal caps the random cocycle Cheeger constant at the inverse triangle count
target: random-complex-cheeger-capped-by-triangle-count
requires: [bounded-removal-finite-quotient-caps-cocycle-cheeger, random-complex-bounded-removal-detected-by-quotient, random-complex-mid-range-pair-properties]
---

## Why sufficient

Fix `0 < η < 1/2`, the integer `t` from the detection claim, `p = n^(-1+η)`, and
`λ = 1/4`. Sample `Y ~ Y(n,p)`.

* **Detection.** A.a.s. there is `T ⊂ Y(2)` with `|T| <= t` such that `Y \ T` is a
  pure connected `1/4`-local spectral expander with the same 1-skeleton, and a
  finite quotient of `π_1(Y \ T)` detects the perimeter of some `Δ in T`.
* **Cap.** Apply `bounded-removal-finite-quotient-caps-cocycle-cheeger` with
  `Y' = Y \ T` and `Z = Y`:
  `h_1(Y,Sym) <= 3|T| / |(Y \ T)(2)| <= 3t / (|Y(2)| - t)`.
* **Triangle count.** By `random-complex-mid-range-pair-properties` (Chapman--Peled
  Corollary 3.2), a.a.s. `|Y(2)| = (1+o(1)) p C(n,3)`, so the cap is
  `O(n^(-3) p^(-1))`.

This is the conclusion of `random-complex-cheeger-capped-by-triangle-count` for
this `η`. Unlike `random-complex-cheeger-capped-via-detecting-quotient`, it needs
no added random triangle and no total-variation transfer, since the cap is
applied to the sampled complex itself.
