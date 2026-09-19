---
rg: 2
id: leavitt-degree3-length7-formal-core-is-diagonal
kind: claim
title: The first degree-three formal long-corner core is only diagonal gluing
artifacts:
  - research/leavitt-degree3-length7-formal-core-diagonal-proof.md
distinct_from:
  leavitt-degree3-length7-formal-core-exists: that detects the nonempty incidence core; this computes its exact Tietze quotient and shows the core has no marked kernel.
---

For the length-seven formal word

```text
t^(-1) x t x t x t^2 x^(-1) t^(-1) x^(-1) t
```

the three Reidemeister--Schreier relations present an infinite cyclic group:
they identify `x_0=x_1=x_2`, and the stable generator is their inverse.
Consequently adjoining a free factor `D` to the formal corner group leaves
`D` embedded.  The nonempty long-corner two-core is a diagonal gluing, not a
kernel witness.
