---
rg: 2
id: wave4-visibility-dual-number-schur-vanishing-proof
kind: route
title: Certify the full congruence kernel and adjoint cohomology vanishing then use the integral LHS spectral sequence
target: wave4-visibility-dual-number-image-is-centrally-closed
requires:
  - ghb7-quotient-image-is-sp4-f7
  - wave3-canonical-k7-class-has-primitive-evaluation
artifacts:
  - research/artifacts/hyperbolic-rf-wave4-visibility-2026-09-20.md
  - experiments/hrf-wave4-dual-number-2026-09-20/dual_number.py
  - experiments/hrf-wave4-dual-number-2026-09-20/dual_number.json
---

Artifact Sections 1-5 give the proof and exact finite arithmetic.
The word (acbc)^24 has nonzero derivative whose adjoint orbit spans
the full ten-dimensional V=sp4(F_7). Thus the actual image equals
V semidirect S with S=Sp4(F_7).

Fifteen independently verified matrix power relations impose rank20
on the30 values of an adjoint cocycle on the three generators.
Coboundaries have rank10, so H^1(S,V)=0; a full presentation of S is
not needed. The trace pairing has rank10 and identifies V with its
dual. Exterior-square invariance constraints have rank45, so
(Lambda^2 V)_S=0. Finite-field chain/cochain duality gives H_1(S,V)=0.

The integral LHS spectral sequence for V->Q->S has zero in all
three total-degree-two entries: H_2(S;Z), H_1(S,V), and
(Lambda^2 V)_S. The first is Steinberg's finite-field central-closure
theorem, with the exact primary citation in the artifact. Hence
H_2(Q;Z)=0. Zero V coinvariants also make Q perfect. The canonical
primitive-evaluation prerequisite then kills its central detectors
by the five-term surjection onto the central image.
