---
rg: 2
id: bounded-removal-detection-from-random-triangle-detection
kind: route
title: Remove the added triangle again, then move the existence event to the random complex by total variation
target: random-complex-bounded-removal-detected-by-quotient
requires: [random-complex-missing-triangle-detected-by-quotient, random-complex-mid-range-pair-properties]
artifacts:
  - research/artifacts/chapman-peled-2509-21566-verified-2026-09-11.md
---

## Why sufficient

Take `t = 1`. Fix `0 < η < 1/2` and `p = n^(-1+η)`. Sample `(Y, Z, Δ)` by
Chapman--Peled's Algorithm 1 (artifact): `Y ~ Y(n,p)`, `Δ` a uniformly random
missing triangle, and `Z = Y ∪ {Δ}`. In the Linial--Meshulam model every edge on
the `n` vertices is present, so `Y` and `Z` share the complete graph as 1-skeleton
and both are connected.

Let `E` be the event about a complex `X` that some `T ⊂ X(2)` with `|T| <= 1`
satisfies conditions 1–3 of `random-complex-bounded-removal-detected-by-quotient`.
`E` depends only on `X`.

1. **Detection.** By `random-complex-missing-triangle-detected-by-quotient`, a.a.s.
   the perimeter of `Δ` survives in some finite quotient of `π_1(Y)`.
2. **Expansion.** By `random-complex-mid-range-pair-properties` (item 3 with
   `λ = 1/4`), a.a.s. `Y` is a `1/4`-local spectral expander.
3. **Purity.** A fixed edge lies in no triangle of `Y` with probability
   `(1-p)^(n-2) <= exp(-p(n-2))`. The expected number of such edges is at most
   `n^2 exp(-(1+o(1)) n^η)`, which tends to `0`. So a.a.s. `Y` is pure.
4. **The event for `Z`.** On the intersection of 1–3, `T = {Δ}` witnesses `E` for
   `Z`, since `Z \ T = Y`. So `E` holds a.a.s. for `Z`.
5. **Transfer.** An a.a.s. property of the complex transfers from `Z` to
   `Y(n,p)`. This is the total-variation transfer recorded on
   `random-complex-mid-range-pair-properties` (Chapman--Peled p. 22). So `E` holds
   a.a.s. for `Y ~ Y(n,p)`.

This is the claim with `t = 1`, at every exponent `η`.
