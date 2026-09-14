---
rg: 2
id: formal-polynomial-strict-pairs-proof
kind: route
title: Linearize at a constant configuration, then invert formally
target: formal-polynomial-strict-pairs-need-unstable-linearization
requires: []
artifacts:
  - research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md
---

Section 2 of the artifact.
1. Translate so that the zero configuration is fixed.
2. Linear parts compose modulo the square of the variable ideal, so `J_sigma(0) J_tau(0) = 1` in
   `M_n(k[G])`. Direct finiteness gives `J_tau(0) J_sigma(0) = 1`.
3. Finite-memory formal maps with zero constant term form a monoid under composition, because each
   degree of a composite uses finitely many terms. A map `id + Q`, with `Q` of order at least two, has
   a right inverse computed degree by degree with finite memory in each degree. Applying the same
   construction to that inverse shows it is two-sided.
4. So `tau` has a two-sided formal inverse `psi`, and `sigma = (sigma o tau) o psi = psi`.
5. Hence `tau o sigma = id` in the completion, and so as polynomials, since both sides are polynomial.
