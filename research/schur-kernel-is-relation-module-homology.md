---
rg: 2
id: schur-kernel-is-relation-module-homology
kind: claim
title: The Schur kernel of an injective nonsingular adjunction is first homology of its relation module modulo third homology
distinct_from:
  aspherical-adjunction-has-zero-schur-kernel: that is the topological statement that an aspherical relative complex kills nothing; this computes the whole Schur kernel algebraically from the relation module, and vanishing of its first homology is the weaker hypothesis.
  nonsingular-adjunction-never-enlarges-schur-multiplier: that proves surjectivity of the second-homology map; this identifies its kernel through the Gruenberg sequence.
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

Let `w in Q * <t>` be nonsingular with injective coefficient map
`q : Q -> X = (Q * <t>)/<<w>>`, and let `M` be the relation module
`<<w>>^ab` as a `ZX`-module. Then

    H_3(Q) -> H_3(X) -> H_1(X; M) -> H_2(Q) --q_*--> H_2(X)

is exact, so `K_2(Q, w) = H_1(X; M)/image H_3(X)`. In particular the Schur
kernel vanishes whenever `H_1(X; M) = 0`, for example when `M` is a free
`ZX`-module.

DERIVATION
schur-kernel-relation-module-proof
