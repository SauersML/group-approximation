---
rg: 2
id: redundant-check-overlay-closes-adjoint-face-gap
kind: route
title: Select the repeated LDPC system with every pairwise redundant check face
target: repeated-ldpc-adjoint-face-hamiltonian-gap
requires:
  - quadratic-redundant-check-overlay-gives-uniform-face-gap
---

Choose the repeated good-LDPC sampler with the overlay `(QRF1)`.  The
quadratic repetition absorbs all new bounded-width occurrences without
changing the scalar coordinate distribution or any private matching.
Equation `(QRF3)` is exactly the required uniform `(GFP3)` for the augmented
face family.
