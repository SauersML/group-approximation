---
rg: 2
id: thompson-v-coset-stabilizers-contain-v-proof
kind: route
title: Recode clopens onto the Cantor set, pick moved points, and read the cosets as restricted inverses
target: thompson-v-coset-stabilizers-contain-copies-of-v
requires: []
artifacts:
  - research/artifacts/thompson-v-coset-peeling-circularity-2026-09-12.md
---

Derivation: Section 2 of the linked artifact.

- **Copies of V.** A finite prefix recoding of a clopen onto `C` conjugates
  `V_U` onto `V`.
- **Separation.** Each nontrivial element moves a nonempty open set. One moved
  point per pair, or a small clopen neighbourhood of it, separates a finite set.
- **Cosets.** `V_D w = V_D w'` exactly when `w^-1` and `w'^-1` agree on
  `C \ D`. Precomposition by `V_(C\D)` is free and commutes with the right action.
- **Infinite alphabet.** Shifting the `N`-coordinate of `(B^N)^G` gives a strict
  continuous equivariant injection over any group.
