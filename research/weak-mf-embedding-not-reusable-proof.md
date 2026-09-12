---
rg: 2
id: weak-mf-embedding-not-reusable-proof
kind: route
title: Import the formalized padding, phase, and irrational-rotation facts
target: weak-mf-embedding-not-reusable
requires: []
artifacts:
  - GroupApproximation/Sofic/NormTraceGap.lean
  - notes/NOTEPAD.md
  - notes/NON_MF_ARCHAEOLOGY.md
---

## Direct proof

Items 1 and 3 are kernel-checked in `GroupApproximation/Sofic/NormTraceGap.lean`
under the declaration names given in the claim; `notes/NON_MF_ARCHAEOLOGY.md`
records that this is what "closed the naive implication weak MF implies
hyperlinear" on 2026-08-08, and that it made rank renormalization the central
design problem.

Item 2 is a two-line verification, recorded in `notes/NOTEPAD.md`: the
representations are exact, so there is no multiplicative defect at all; the
operator-norm distance of `diag(exp(i k theta),1,...,1)` from `1` is
`|exp(i k theta)-1|`, bounded below along the whole group by irrationality of
`theta`; and its squared normalized Hilbert--Schmidt distance from `1` is
`|exp(i k theta)-1|^2/n -> 0`.  End proof.

## Reading

The archaeology entry deserves care: what was closed in August 2026 is the
*route*, not the statement.  `mf-implies-hyperlinear` remains open, and the
present claim is exactly the reason its proof cannot be a computation inside
one given model.
