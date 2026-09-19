---
rg: 2
id: atlas-m2-coefficient-substitution-wall-proof
kind: route
title: Correct the approximate M2 table and amplify the rank-one q14 defect
target: atlas-m2-coefficient-substitution-cannot-dilute-q14
requires:
  - atlas-packet-collision-m2-has-full-coefficient-algebra
  - atlas-rank-stability-literature-fence
  - atlas-multiplicity-two-joint-kernel-slice-is-empty
---

Finite-algebra rank stability corrects the four approximate matrix units to
an exact `M_2(F2)` representation at flexible `o(d)` cost.  Every exact
module is a standard two-dimensional amplification.  Fixed-word
rank-Lipschitzness transfers the correction to the Atlas residuals.  The
stored q14 defect has rank one in dimension eight, so its `k`-fold exact
amplification has rank `k` in dimension `8k`; the limiting normalized floor
is `1/8`.
