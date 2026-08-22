---
rg: 2
id: central-sign-bcs-energy-terminal-proof
kind: route
title: Renormalize the decoded negative corner and apply the robust BCS gap
target: central-sign-bcs-energy-decoder-implies-nonhyperlinear
requires:
  - central-involution-corner-exactification
  - non-ce-bcs-has-robust-approximate-energy-gap
---

Canonical microstates make the rounded central-sign projection have trace
tending to `1/2`.  The BCS energy computed with ambient normalized trace is
its corner-normalized energy multiplied by that trace.  Hence the robust BCS
gap gives `E_B^amb>=beta_B tau(Q)`, while the decoder bound makes the same
quantity tend to zero with the presentation defect.  The exact `J=-I`
representation proves that the marked involution is nontrivial, yielding the
contradiction to hyperlinearity.

