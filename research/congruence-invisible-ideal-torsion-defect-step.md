---
rg: 2
id: congruence-invisible-ideal-torsion-defect-step
kind: claim
title: If the congruence kernel of an ideal is MF-invisible, a torsion one-sided pair modulo that ideal puts its defect ideal in the MF radical
distinct_from:
  finite-additive-order-one-sided-defects-are-mf-invisible: that is the absolute statement for a one-sided pair of the ring itself; this transports it through a quotient ring whose congruence kernel is already MF-invisible.
artifacts:
  - research/artifacts/un-open-1-hilbert-hotel-radical-2026-09-13.md
---

**ESTABLISHED** (route `congruence-invisible-ideal-torsion-defect-step-proof`), unreviewed.

Let `R` be a countable unital ring, `J` a two-sided ideal and `n >= 4`. Suppose

```text
EL_n(R) n GL_n(R,J) <= Rad_MF(EL_n(R)),     ts - 1 in J,     m(1 - st) in J for some m >= 1.
```

Then `EL_n(R, ReR + J) <= Rad_MF(EL_n(R))`, where `e = 1 - st`.

The proof uses no matrix identity in a quotient group: it passes to the ring `R/J`, where the pair is a
genuine one-sided pair, and pulls the absolute statement back. The hypothesis is strictly stronger than
`EL_n(R,J) <= Rad_MF(EL_n(R))`, and the difference matters: see the `A_m` calibration in
`relative-torsion-defect-mf-radical-step`.
