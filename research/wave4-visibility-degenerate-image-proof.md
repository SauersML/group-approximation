---
rg: 2
id: wave4-visibility-degenerate-image-proof
kind: route
title: Span the congruence root vector under the constant Heisenberg image and identify its invariant coordinate character
target: wave4-visibility-degenerate-dual-number-image
requires:
  - cckw-ghb2-kms-group-structure
artifacts:
  - research/artifacts/hyperbolic-rf-wave4-visibility-2026-09-20.md
  - experiments/hrf-wave4-dual-number-2026-09-20/dual_number.py
  - experiments/hrf-wave4-dual-number-2026-09-20/dual_number.json
---

Artifact Section6 gives the proof. A and B are constant matrices
generating the known vertex U of order343. C_t=I+tE_31 generates
under their conjugates a congruence subgroup whose additive orbit
span has exactly dimension10. Thus Q_0=V semidirect U.

The adjoint difference span on V has rank9; its invariant quotient
coordinate is lambda(X)=X_31, with lambda(E_31)=1. Hence V_U=C7
and Q_0^ab=V_U directsum U^ab=C7^3. Combining lambda with the
Heisenberg character A,B->1 gives chi_0, and surjectivity of GHB7
onto Q_0 identifies the K7 image with its index-seven kernel.
