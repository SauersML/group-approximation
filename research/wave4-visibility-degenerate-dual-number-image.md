---
rg: 2
id: wave4-visibility-degenerate-dual-number-image
kind: claim
title: The degenerate CCKW dual-number image is a ten-dimensional adjoint module extended by the order343 Heisenberg group
distinct_from:
  wave4-visibility-dual-number-image-is-centrally-closed: That identifies the nondegenerate z=1+t image and computes its multiplier; this identifies the different z=t image and its index-seven K7 subgroup without claiming multiplier vanishing there.
artifacts:
  - research/artifacts/hyperbolic-rf-wave4-visibility-2026-09-20.md
  - experiments/hrf-wave4-dual-number-2026-09-20/dual_number.py
  - experiments/hrf-wave4-dual-number-2026-09-20/dual_number.json
---

For R=F_7[t]/(t^2), the CCKW x=y=1,z=t image is

    Q_0=V semidirect U,

where V=sp4(F_7) is additive of dimension10 and U=<A,B> is the
Heisenberg group of order7^3. Thus |Q_0|=7^13 and Q_0^ab=C7^3.

The character GHB7->C7 sending a,b,c to1 descends to

    chi_0((I+tX)h)=X_31+chi_U(h),  chi_U(A)=chi_U(B)=1.

The K7 image is exactly ker chi_0, of order7^12, with intersection
ker(X->X_31) of dimension9 inside V and surjection onto U.

No Schur-multiplier or canonical centre-detection conclusion for
this degenerate image is asserted.

DERIVATION
wave4-visibility-degenerate-image-proof
