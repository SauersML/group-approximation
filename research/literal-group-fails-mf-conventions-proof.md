---
rg: 2
id: literal-group-fails-mf-conventions-proof
kind: route
title: Central-involution proof of simultaneous MF failure
target: literal-group-fails-mf-conventions
requires: [countable-group-mf-conventions, literal-central-mark-corona-invisible]
artifacts:
  - non_mf_groups_exist.tex
  - notes/NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md
  - GroupApproximation/Sofic/LiteralNonMFPresentation.lean
  - GroupApproximation/Sofic/LiteralNonMFEndpoint.lean
  - GroupApproximation/Sofic/MFRepresentationVariants.lean
---

## Why sufficient

The claim `literal-central-mark-corona-invisible` gives a nontrivial marked
element killed by every genuine positive natural-dimension norm-matrix
C-star-corona representation, so `E` is not operator MF.  The equivalent MF
formulations fail by `countable-group-mf-conventions`; every listed stronger
convention fails because its approximation data has a proved forgetful
implication to operator MF.  The complete conjunction is exposed by
`literal_failsEveryStandardMFConvention`.
