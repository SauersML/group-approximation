---
rg: 2
id: hnn-outlier-exclusion-from-closed-a2-loop
kind: route
title: Round the free HNN letter and close it using the two shortest A2 returns
target: sl3-ambient-outliers-carry-no-free-hnn-letter
requires:
  - hnn-stable-letter-rounds-to-finite-order
  - one-mixed-a2-word-does-not-control-fold-square
  - two-torus-closures-detect-denominator-multiplicity
---

**INVALIDATED PROPOSAL.**  Spectrally round the amalgamated-free Haar letter
to the balanced involution supplied by
`hnn-stable-letter-rounds-to-finite-order`.  Then combine the unbalanced
torus word with both shortest `A_2` paths to the highest root,

```text
W_12 E_23 W_12^*=[E_12,E_23]=W_23^*E_12W_23,
```

and attempt to force the involution's denominator fold square to one.

`closed-a2-loop-still-leaves-swap-fold-free` gives exact finite packets in
which every equality used by this proposal has zero defect but the fold
square stays a fixed distance `sqrt(3)` from one.  Therefore those two mixed
returns do not supply the missing estimate, even after the Haar-to-involution
reduction.  This does not invalidate a proof using further lattice relations
or the genuinely full amalgamated-free moment law; those are exactly the
remaining inputs absent from the packet.
