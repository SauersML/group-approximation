---
rg: 2
id: leavitt-rank-triviality-via-commutant-rank-distortion
kind: route
title: A model-independent distortion of commutant ranks on a defect range contradicts commutant faithfulness at near-minimal defect, so the binary Leavitt unit group has no nontrivial characteristic-two rank model
target: non-linear-sofic-group
requires:
  - some-commutant-element-distorts-defect-range-rank
  - near-minimal-defect-ranges-are-rank-faithful-for-the-commutant
  - leavitt-rank-model-defect-gap-on-fixed-point-free-quotients
artifacts:
  - research/artifacts/halving-expansion-and-commutant-faithfulness-2026-09-12.md
---

Artifact Proposition 2.3(1).

1. **Positive infimum.** If a nontrivial characteristic-two rank model of `R^x` exists, its
   fixed-point-free quotient is nontrivial, so the infimum `c_*` of normalized defects over nontrivial
   fixed-point-free models is positive (`leavitt-rank-model-defect-gap-on-fixed-point-free-quotients`).
2. **Near-minimal model.** Choose one with `delta <= (1+eps) c_*` and `eps < kappa`. By
   `near-minimal-defect-ranges-are-rank-faithful-for-the-commutant`, every `Z` in `M_n(C_U)` has
   `|rk(D_Theta Z) - delta rk(Z)| <= eps delta/(1+eps) < kappa delta`.
3. **Contradiction** with `some-commutant-element-distorts-defect-range-rank`. So every model is trivial.
4. **Payoff.** An `F_2`-linear sofic approximation of the infinite group `R^x` gives a nontrivial model,
   so `R^x` is not `F_2`-linear sofic.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 13.2 (conditional on the open distortion claim) of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
