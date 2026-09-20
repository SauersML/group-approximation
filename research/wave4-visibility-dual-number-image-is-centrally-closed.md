---
rg: 2
id: wave4-visibility-dual-number-image-is-centrally-closed
kind: claim
title: The nondegenerate CCKW dual-number image is full Sp4 over the dual numbers and has trivial entire Schur multiplier
distinct_from:
  wave3-visibility-cckw-matrix-maps-lift-to-steinberg: That excludes stable Steinberg pushout classes for all CCKW maps; this computes the entire Schur multiplier of one actual finite image and excludes every central extension of that image.
  wave3-visibility-canonical-centre-blind-to-steinberg-and-sp4: That treats full finite-field symplectic images; this adds the full first-order congruence image with its ten-dimensional normal congruence subgroup.
artifacts:
  - research/artifacts/hyperbolic-rf-wave4-visibility-2026-09-20.md
  - experiments/hrf-wave4-dual-number-2026-09-20/dual_number.py
  - experiments/hrf-wave4-dual-number-2026-09-20/dual_number.json
---

Put R=F_7[t]/(t^2). The CCKW matrices with x=y=1,z=1+t generate
Q=Sp_4(R), of order 7^10*276595200. The image of K7 is also all of Q.
The group Q is perfect and H_2(Q;Z)=0, hence H^2(Q;F_7)=0.

Consequently if a finite image F of the canonical extension B_c0 has
F/<image(z)> isomorphic to Q, then image(z)=1. No reduction c0 mod m
with m>1 inflates along this CCKW K7 quotient. This excludes all central
extensions of the actual image, not only stable Steinberg pushouts.

No conclusion is asserted for proper subgroups, the degenerate z=t
image, or arbitrary finite quotients.

DERIVATION
wave4-visibility-dual-number-schur-vanishing-proof
