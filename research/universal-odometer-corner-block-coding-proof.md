---
rg: 2
id: universal-odometer-corner-block-coding-proof
kind: route
title: Block-code the constant-return system and divide its cyclic coordinates
target: universal-odometer-corners-preserve-kazhdan-hosts
requires:
  - simple-kazhdan-lef-group-from-minimal-subshift
  - odometer-matrix-towers-host-locally-finite-groups
artifacts:
  - research/artifacts/pestov91-universal-host-finite-centralizers-2026-09-13.md
---

Section 1 supplies the dynamical and ring proofs. The return time to the
zero cell is exactly `m`. Length-`m` block coding is an injective conjugacy
onto a finite-alphabet subshift; density of the original orbit gives
minimality of the return system. The coordinates `pi_(mn)/m mod n` give
its compatible cyclic factors and their inverse limit is onto by
compactness. Only exponents divisible by `m` survive compression by `q`,
which identifies the corner crossed product. Apply the two required
claims to that system, using the trivial scalar centre over `F_2`.
