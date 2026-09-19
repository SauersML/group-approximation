---
rg: 2
id: hyperlinear-not-imply-mf
kind: claim
title: Hyperlinearity does not imply the MF property
distinct_from:
  mf-implies-hyperlinear: This established separation refutes the direction hyperlinear implies MF; the open claim asks for the converse direction under the weak norm-corona MF convention.
  weakly-sofic-not-sofic: This separates hyperlinearity from the operator-norm MF property; the other separates weak soficity from soficity. Different pairs of classes, different witnesses, no shared content beyond both being separations.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Endpoint/NonMFImpact.lean
  - GroupApproximation/Endpoint/Audit.lean
  - GroupApproximation/Endpoint/Public.lean
  - notes/NON_MF_IMPACT_FORMAL_STATUS.md
  - notes/NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md
---

There exists a hyperlinear group that is not MF; the concrete witness may be
taken to be the finitely generated group `W`.  This is the premise-free Lean
theorem `GroupApproximation.NonMFImpact.witness_hyperlinear_nonMF`.
