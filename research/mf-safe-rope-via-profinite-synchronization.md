---
rg: 2
id: mf-safe-rope-via-profinite-synchronization
kind: route
title: Synchronize the correct rope edge in finite quotients
target: mf-safe-asymmetric-hnn-replacement
requires:
  - profinite-synchronized-hnn-is-regular-mf
  - positive-rope-profinite-edge-synchronization
---

Use the unchanged Higman rope presentation, so Britton's lemma still embeds
`Q=F/N` and the finite branch retains the fixed non-MF group.  On the infinite
branch, apply `profinite-synchronized-hnn-is-regular-mf` to the cofinal
quotient family supplied by `positive-rope-profinite-edge-synchronization`.
Condition `(RPS1)` is exactly the hypothesis `(PSH2)` for the graph edge, so
the final HNN extension is MF.  The construction is effective by the uniform
clause of the synchronization claim.

