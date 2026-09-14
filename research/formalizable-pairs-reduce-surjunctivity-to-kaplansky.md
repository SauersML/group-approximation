---
rg: 2
id: formalizable-pairs-reduce-surjunctivity-to-kaplansky
kind: route
title: An injective binary automaton has a left inverse; formalize the pair and linearize
target: stable-finiteness-forces-binary-surjunctivity
requires:
  - binary-left-inverse-pairs-are-formalizable
  - formal-polynomial-strict-pairs-need-unstable-linearization
artifacts:
  - research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md
---

1. **Left inverse.** Let `tau` be injective on `(F_2^n)^G`. By compactness there is a finite `S` such
   that `x(1)` is determined by `tau(x)|_S`. Define a local rule on the patterns that occur, extend it
   arbitrarily to all patterns, and get an automaton `sigma` with `sigma o tau = id`.
2. **Formalize.** By the first prerequisite, some representatives satisfy the identity formally.
3. **Linearize.** Stable finiteness of `F_2[G]` makes `M_n(F_2[G])` directly finite. By the second
   prerequisite, `tau o sigma = id`, so `tau` is surjective.
