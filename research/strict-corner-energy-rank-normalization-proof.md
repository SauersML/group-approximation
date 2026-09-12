---
rg: 2
id: strict-corner-energy-rank-normalization-proof
kind: route
title: Transfer the robust contraction energy gap through every surviving matrix-corona corner
target: strict-bcs-energy-in-augmentation-corner-kills-mf
requires:
  - non-ce-bcs-has-robust-approximate-energy-gap
  - matrix-corona-projection-ideal-and-corner-calculus
  - nonhyperlinear-finite-augmentation-corner-kills-mf
artifacts:
  - research/artifacts/strict-bcs-energy-in-full-augmentation-corner-2026-09-08.md
---

Round self-adjoint matrix contractions to their spectral signs.
The normalized HS distance is bounded by the square-defect norm.
Telescoping contextual commutators and forbidden products then bounds
the existing robust unitary energy by a fixed constant times the
contraction energy. Thus the latter has a positive gap in every
matrix algebra and in every tracial matrix ultraproduct.

If a norm-corona representation retained `q`, its nonzero corner
would map unitally to a tracial matrix ultraproduct after normalization
by its own coordinate ranks. The displayed contraction tuple would
have trace energy at least `beta`, contradicting the preserved order
bound `E_B(a)<=c q` with `c<beta`. Thus `q` is killed, and the
finite average identity forces every element of `K` to be killed.

A hyperlinear host gives the same contradiction using its normalized
canonical corner trace, whose mass is `1-1/|K|>0`. This proves the
claimed additional obstruction to hyperlinear hosts.

The finite-support certificate and the maximal C-star map consequence
are proved in Sections 3 and 4 of the artifact. They retain the
actual corner and do not use a quotient-only realization of the BCS.
