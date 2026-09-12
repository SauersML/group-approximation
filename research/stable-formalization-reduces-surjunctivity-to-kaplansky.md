---
rg: 2
id: stable-formalization-reduces-surjunctivity-to-kaplansky
kind: route
title: Stabilize by identity ancilla tracks, formalize a left inverse, and linearize
target: stable-finiteness-forces-binary-surjunctivity
requires:
  - injective-binary-automata-are-stably-formalizable
  - formal-polynomial-strict-pairs-need-unstable-linearization
artifacts:
  - research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md
---

1. Let `tau` be injective on `(F_2^n)^G`. Then `tau x id` on `(F_2^(n+m))^G` is injective, and it is
   surjective iff `tau` is.
2. By the first prerequisite, some `m` and some left inverse `sigma'` of `tau x id` have
   representatives with `sigma' o (tau x id) = id` formally.
3. Stable finiteness of `F_2[G]` makes `M_(n+m)(F_2[G])` directly finite. By the second
   prerequisite, `tau x id` is bijective, so `tau` is surjective.
