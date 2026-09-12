---
rg: 2
id: non-rf-hyperbolic-via-central-rips-pullback
kind: route
title: Construct invisible central prime torsion from a Rips input with restricted finite quotient centers
target: non-residually-finite-hyperbolic-group
requires:
  - hyperbolic-finite-images-exclude-a-central-prime
  - hyperbolic-rf-central-prime-center-equivalence
artifacts:
  - research/artifacts/rips-central-pullback-finite-image-centers-2026-09-12.md
---

Choose the prime `p` and the non-elementary hyperbolic input `H` supplied
by the first prerequisite. Apply assertion 2 implies assertion 1 of the
second prerequisite for this fixed `p`. Concretely, take a hyperbolic Rips
extension of `Sp_4(Z)` whose kernel is a quotient of `H`, then pull back
Deligne's central `C_(2p)` cover. Its central order-`p` mark survives as a
group element and vanishes in every finite image. The pullback is
word-hyperbolic, so it is the required counterexample.

The unproved prerequisite is the explicit hyperbolic input `H` with the
specified restriction on **every** finite quotient center.
