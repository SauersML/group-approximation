---
rg: 2
id: kazhdan-hyperbolic-b2-group-flexibly-hs-stable
kind: claim
title: Some hyperbolic Kazhdan group with positive second Betti number is flexibly Hilbert--Schmidt stable
distinct_from:
  kazhdan-weak-ucp-stability-is-flexible-stability: that identifies weak ucp-stability with flexible HS-stability for hyperlinear Kazhdan groups; this asks for flexible HS-stability of one hyperbolic Kazhdan group with b_2 >= 1, which that equivalence may be used to restate
  random-complex-linear-cocycle-stability: that is a permutation cocycle-stability estimate for random complexes; this is unitary stability of a group, with no Hamming metric and no randomness required
---

**OPEN, conjectural.** There is a word-hyperbolic group `Γ` with property (T) and
`b_2(Γ;Q) >= 1` that is flexibly Hilbert--Schmidt stable. Every asymptotic
representation in normalized Hilbert--Schmidt norm is close, after enlarging the
dimension, to a genuine representation.

By `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity` this gives a
non-hyperlinear hyperbolic group, which is both nonsofic and not residually finite.

## Candidates (not source-verified in this node)

* **Gromov density-model random groups at density in `(1/3, 1/2)`.** They are
  Kazhdan and hyperbolic. If the presentation complex is aspherical,
  `b_2 = #relators - #generators >= 1`. Dogon's 2023 theorems already list them
  for the infinite cyclic extension; see
  `kazhdan-weak-ucp-stability-is-flexible-stability`.
* **Mid-range Linial--Meshulam groups `π_1(Y(n, n^(-1+η)))`.** They are hyperbolic
  and Kazhdan a.a.s. (`random-complex-mid-range-pair-properties`, plus Garland--Żuk
  for λ < 1/2), with `b_2(Y) = χ(Y) - 1 ~ p·C(n,3)`. For `b_2(π_1 Y)` one must
  still bound the image of `π_2(Y)` (Hopf).

## What it cannot be

Strict HS-stability is excluded for every infinite hyperlinear Kazhdan group by
Becker--Lubotzky, so only the flexible notion is available. Reading the claim
contrapositively: if all hyperbolic groups are hyperlinear, this claim is false.
