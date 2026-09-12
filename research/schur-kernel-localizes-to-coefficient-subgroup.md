---
rg: 2
id: schur-kernel-localizes-to-coefficient-subgroup
kind: claim
title: The Schur kernel of a nonsingular adjunction is pushed forward from the coefficient subgroup
distinct_from:
  kl-failure-localizes-to-the-coefficient-subgroup: that localizes the degree-zero coefficient kernel through the same pushout; this localizes the second-homology kernel, using the Mayer--Vietoris sequence of the amalgamated product.
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

Let `w in Q * <t>` be nonsingular, and let `B <= Q` contain its
coefficients with `B -> (B * <t>)/<<w>>` injective. Then

    K_2(Q, w) = iota_*( K_2(B, w) ),    iota : B -> Q.

A class of `H_2(Q)` is killed by the adjunction only if it is the image of a
class of the coefficient subgroup that is already killed there.

DERIVATION
schur-kernel-localization-proof
