---
rg: 2
id: stable-formalizability-reduces-prime-power-surjunctivity
kind: route
title: Take a left inverse, stabilize until the pair is formal, and linearize under stable finiteness
target: stable-finiteness-forces-prime-power-surjunctivity
requires:
  - prime-field-left-inverse-pairs-are-stably-formalizable
  - formal-polynomial-strict-pairs-need-unstable-linearization
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
---

1. **Left inverse.** An injective `tau` on `(F_p^n)^G` has a left-inverse automaton `sigma`, by compactness.
2. **Stabilize.** The first prerequisite gives `k` with `(tau (+) id_k, sigma (+) id_k)` formalizable.
3. **Linearize.** Stable finiteness of `F_p[G]` makes `M_(n+k)(F_p[G])` directly finite, so the second
   prerequisite makes `tau (+) id_k` bijective. Hence `tau` is surjective.
