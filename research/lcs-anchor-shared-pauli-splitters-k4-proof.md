---
rg: 2
id: lcs-anchor-shared-pauli-splitters-k4-proof
kind: route
title: Extend edge diagonal forms over the common vertex space and realize all gates by Pauli translations
target: lcs-anchor-shared-pauli-splitters-have-k4-model
requires:
  - lcs-pc-zero-noise-coloring-cheat
artifacts:
  - research/artifacts/lcs-anchored-attack-2026-09-20.md
---

The artifact supplies the exact candidate equations, honest operator
extension, and countermodel. The common vertex space has basis Omega and
two colour vectors for each of four vertices. Its symmetric bilinear
form has identity blocks within vertices and cyclic-permutation blocks
between vertices. Each edge has six allowed atom vectors; their row and
column sums span dimension five and embed isometrically into the common
vertex space. Adjoining one vector per edge extends all six local forms,
giving a fifteen-dimensional binary bilinear space.

On its finite regular Hilbert space, use translations X_v and phase
operators Z_v defined by the form. Their commutator is the scalar
(-1)^b(v,w). Context orthogonality and vector marginal sums verify every
displayed relation, including the full local subset table. The diagonal
form equals pairing with Omega, verifying the common-anchor covariance.
All three vertex atom signs are negative, while one zero-sign edge atom
still has a nonidentity translation. Thus the proposed decoder fails.

Tensor powers of the binary space preserve context orthogonality,
normalization, and marginals. They give the stated finite models for
every repetition count. The prerequisite supplies the unrestricted
source gap and its decay under projection-game repetition, so no uniform
positive source decoder can exist for the candidate.
