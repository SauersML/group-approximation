---
rg: 2
id: non-rf-hyperbolic-via-kms-reflected-root-word
kind: route
title: Separate the geometric nontriviality of a KMS root word from its finite-image vanishing
target: non-residually-finite-hyperbolic-group
requires:
  - kms-hc1-reflected-root-word-is-nontrivial
  - kms-hc1-finite-images-kill-reflected-root-word
artifacts:
  - research/artifacts/kms-hc1-marked-root-kernel-candidate-2026-09-12.md
---

Choose the prime `p>=7` supplied by the finite-image claim. The geometric
claim gives the explicit infinite word-hyperbolic group `Gamma_p` and a
nontrivial element `w_p` of infinite order. Every homomorphism from
`Gamma_p` to a finite group sends its generators to a triple satisfying
the defining relators, so the finite-image claim makes its value on
`w_p` the identity. Thus `w_p` is a nontrivial element of the finite
residual of `Gamma_p`, proving that `Gamma_p` is not residually finite.

The universal finite-image claim is the open input of this route. The
canonical positive Kac--Moody quotient and the block-matrix computations
do not discharge that input.
