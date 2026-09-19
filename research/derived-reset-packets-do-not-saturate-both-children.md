---
rg: 2
id: derived-reset-packets-do-not-saturate-both-children
kind: claim
title: Balanced derived-reset packets do not saturate both child sources
distinct_from:
  authenticated-pauli-branch-needs-source-saturation: that proves the analytic recurrence once two full-source moments are supplied; this audits whether the existing Pauli, derived-reset, and Schur packets actually supply those moments.
  pauli-two-child-transfer-packet: that constructs two exact equal-source arrows from a smaller source into a doubled target; this proves why the existing balanced reset cannot return that doubled target to the same source scale.
  branch-flip-pauli-extraction-cancels-schur-surplus: that shows the Pauli flip consumes the Schur factor two; this expresses the same cancellation as a sharp source-Gram rank obstruction for the PAZ return.
---

If a reset carrier has rank `2n` and a child range has rank at most `n`, every
contraction into that child obeys

```text
||S^*S-P||_2^2 >= 1/2
```

in corner-normalized trace, or at least `tau(P)/2` ambiently.  The existing
balanced Pauli/Schur reset therefore doubles the target but cannot saturate
both children from the full returned source.  A matrix-only proper-corner
return is still required.
