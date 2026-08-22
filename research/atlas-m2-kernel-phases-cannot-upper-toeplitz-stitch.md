---
rg: 2
id: atlas-m2-kernel-phases-cannot-upper-toeplitz-stitch
kind: claim
title: Multiplicity-two kernel phases cannot stitch across an upper-Toeplitz domain wall
distinct_from:
  atlas-multiplicity-two-joint-kernel-slice-is-empty: that is the finite phase calibration; this proves that arbitrary upper-triangular couplings of those calibrated phases cannot dilute both residual ranks.
  folner-multiplicity-atlases-have-vanishing-first-exit: that constructs coherent rectangular multiplicity transports for a finite translation stencil; this shows the Atlas kernel Laurent words retain every diagonal phase defect under flag-preserving stitching.
  atlas-even-gram-does-not-pay-toeplitz-exit: that concerns complex tracial Gram coordinates in a Schur Toeplitz head; this is an exact defining-characteristic rank obstruction for two concrete Atlas phases.
artifacts:
  - experiments/atlas-a4-repeated-module-screen.json
---

Fix one marking parity and choose multiplicity-two packet frames of two types:

```text
A: q_19243(A)=I,   rank(q_14(A)-I)=1,
B: q_14(B)=I,      rank(q_19243(B)-I)=2.              (UTS1)
```

These are exactly the two pure zero fibers in the calibrated F4-seeded slice.
Let `T` be any invertible block-upper-triangular stitching of `N` such phases,
with arbitrary off-diagonal blocks, and let all fixed chart coefficients and
seed frames be block diagonal.  Suppose `n_A` diagonal blocks have type A and
`n_B=N-n_A` have type B.  Then

```text
rank(q_14(T)-I)       >= n_A,
rank(q_19243(T)-I)    >= 2 n_B.                       (UTS2)
```

Consequently

```text
max(rank(q_14(T)-I),rank(q_19243(T)-I)) >= 2N/3,      (UTS3)
```

and the sum of the two ranks is at least `N`.  Thus nilpotent upper-shift or
block-Toeplitz coupling cannot localize the joint incompatibility to an
`O(1)` domain wall: at least one residual has positive rank density.

This is deliberately a phase-stitching theorem, not the amplified Atlas gap.
A cyclic/non-flag-preserving gauge has no diagonal quotient on which to read
`(UTS1)`, and a genuinely new bulk phase need not be assembled from A/B
blocks.  Those are the only surviving Følner escape formats after `(UTS3)`.
