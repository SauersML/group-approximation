---
rg: 2
id: wave4-visibility-marked-lie-four-generator-elimination
kind: claim
title: Two face differences eliminate two generators from the marked K7 Lie presentation by a unique filtration-contractive solution
distinct_from:
  wave4-visibility-k7-marked-face-presentation: That gives the exact group presentation and central marking; this proves an isomorphism reducing its truncated Lie calculations from six free generators to four.
artifacts:
  - research/artifacts/hyperbolic-rf-wave4-filtered-elimination-2026-09-20.md
  - experiments/hrf-wave4-four-generator-2026-09-20/eliminate.py
  - experiments/hrf-wave4-four-generator-2026-09-20/class_4.json
  - experiments/hrf-wave4-four-generator-2026-09-20/class_5.json
  - experiments/hrf-wave4-four-generator-2026-09-20/class_6.json
  - experiments/hrf-wave4-four-generator-2026-09-20/class_five_lie_witness.json
---

For 2<=C<7, let R_i be the class-C BCH logarithm of the marked
three-corner face word and E=R_2-R_1,F=R_3-R_1. In the free class-C
Lie algebra on U0,V0,U1,V1, start T=-U0-U1,W=-V0-V1 and repeat

    T <- T-4E+(3/2)F, W <- W-2E+F

simultaneously after substituting U2=T,V2=W. After C-1 iterations
the solution is exact and unique. Hence freeLie6/ideal(E,F) is
isomorphic to freeLie4, preserving the four named generators.
Substitution of every remaining relation gives the identical marked
quotient, not merely a quotient of it.

The exact script yields quotient dimensions 17,28,45 in classes
4,5,6; the central mark is zero only in class4. The class5 result
is independently reproduced by the six-generator implementation.

DERIVATION
wave4-visibility-filtered-elimination-proof
