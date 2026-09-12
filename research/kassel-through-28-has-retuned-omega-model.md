---
rg: 2
id: kassel-through-28-has-retuned-omega-model
kind: claim
title: Kassel relations through 2.8 together with 2.12 have an exact retuned 24-dimensional omega model
artifacts:
  - research/artifacts/kassel-through-28-retuned-omega-model-2026-08-21.md
distinct_from:
  kassel-27-28-charge-the-explicit-omega-packet: that proves a positive defect floor after freezing the first permutation packet; this retunes that packet and makes both relations exact.
  kassel-four-cell-has-exact-omega-model: that satisfies only the first determinant-holonomy four-cell; this additionally satisfies the simultaneous coupling pair (2.7)--(2.8).
  maslov-mod3-projective-defect-gap: that concerns the full Deligne presentation; this countermodel stops before (2.9) and the remaining mixed relations.
---

There is an explicit representation on `C^24` satisfying Kassel relations

```text
(2.4), (2.5), (2.6), (2.7), (2.8), (2.12)
```

exactly and having `w_beta^4=omega I_24`.  It uses a retuned four-point
permutation packet and a diagonal six-clock gauge.  Therefore the positive
floor found for (2.7)--(2.8) on the earlier frozen packet is not universal,
and no normalized-HS inequality supported on these six relators can collapse
the marked word.

The next sequential relation (2.9) has defect exactly one on this packet;
whether it can be absorbed by another retuning remains separate.

`kassel-29-defeats-scalar-and-single-clock-retunings` shows that neither
tensoring/conjugating this packet nor freeing the middle root by one cyclic
Weyl clock can absorb (2.9).  A noncyclic middle-root packet or non-scalar
`x_(-beta)` remains possible.
