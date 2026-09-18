---
rg: 2
id: kt-sandwich-from-kernel-polynomiality
kind: route
title: Polynomiality of Mon-stable kernel overgroups gives the compressor sandwich
target: kt-compressor-stable-polynomial-content-overgroups-are-gamma
requires:
  - kt-compressor-stable-kernel-overgroups-are-polynomial
  - kt-compressor-sandwich-equivalent-to-kernel-polynomiality
---

Let `Δ` be admissible. Its kernel `H = Δ ∩ EL_r(R)` is admissible
(`kt-compressor-sandwich-equivalent-to-kernel-polynomiality` Part 1). By
`kt-compressor-stable-kernel-overgroups-are-polynomial`, `H ≤ SL_r(A)`, and Part 2 of the
equivalence gives `π(Δ) = {I}` and `Δ = Γ`. The converse direction is also in that claim,
so this route loses nothing.
