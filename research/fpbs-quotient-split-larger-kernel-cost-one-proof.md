---
rg: 2
id: fpbs-quotient-split-larger-kernel-cost-one-proof
kind: route
title: Close the sparse normal-subgroup graphing under normalizing lifts at small markers, then lift the quotient graphing fibre by fibre
target: fpbs-quotient-split-larger-kernel-cost-one
requires:
  - fpbs-small-marker-induction-input
  - fpbs-normalized-cost-induction-input
artifacts:
  - research/artifacts/fpbs/normal-finite-cost-rank-gradient-2026-09-17.md
---

Written proof in Section 2 of the linked note: Lemmas 2.1 and 2.2 and the four graphings Φ1, Φ1', Φ2, Φ3, of total measure at most `1 + (K+1)δ + 2ε`. It uses:

* small complete sections of aperiodic relations;
* the complete-section induction formula for `R_sigma|A`;
* the Feldman--Moore splitting of a partial isomorphism of a free action's orbit relation into pieces given by single group elements.

The third is standard and used in the same way by `fpbs-quotient-split-actions-cost-one-proof`. This is dependency bookkeeping for a written deduction, not a formal verification.
