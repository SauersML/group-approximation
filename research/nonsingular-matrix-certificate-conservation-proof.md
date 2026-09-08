---
rg: 2
id: nonsingular-matrix-certificate-conservation-proof
kind: route
title: Compute the unitary power-map degree and solve the added relator exactly
target: nonsingular-equations-preserve-matrix-certificates
requires: []
artifacts:
  - research/artifacts/nonsingular-equations-and-approximation-radicals.md
  - experiments/nonsingular_equation_audit.py
  - research/artifacts/nonsingular-equation-replay.json
---

Sections 1--2 give the complete argument. Deform the coefficient matrices
to the identity, obtaining the power map `T -> T^m`. A target with distinct
eigenvalues has exactly `|m|^d` roots. The derivative on diagonal tangent
directions and complex off-diagonal planes shows that its degree is
`m^d`, including negative `m` by the orientation sign of inversion.
Nonzero degree proves an exact root exists in every dimension.

For each coefficient tuple choose that root; the added defect vanishes
without changing any coefficient. This proves equality of the admissible
constant sets, including their infinite-infimum case. Section 6 then
evaluates an arbitrary finite normal-closure identity at the root and
telescopes only its old-relator factors to prove the quantitative cost bound.

Section 8 documents the exact finite replay. It checks degree signs and
noncommutative examples and rejects a singular negative control. The
all-dimensions theorem is proved in Sections 1--2, independently of the
finite replay.
