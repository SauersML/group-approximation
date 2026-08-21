---
rg: 2
id: average-blr-self-correction-narrows-bounded-template-decoder
kind: route
title: Upgrade average occurrence BLR energy before abelian rounding
target: bounded-template-all-pairs-additive-decoder
requires:
  - bounded-template-average-blr-occurrence-decoder
  - unitary-blr-average-self-corrects-uniformly
---

Apply the occurrence decoder to obtain `(BTA1)`, then apply polar BLR
self-correction.  Equations `(UBA2)--(UBA3)` change the table by a
dimension-free average modulus and produce the maximum-over-all-pairs
almost-action `(BAT1)` on the same Hilbert space.  This is precisely the input
to `finite-abelian-hs-almost-actions-round-in-the-same-dimension`.

