---
rg: 2
id: sparse-face-row-square-survives-intrinsic-green-step
kind: claim
title: Sparse face and equality layers remain in the row-square basin under the intrinsic Green step
distinct_from:
  dense-complete-pair-remainders-are-cb-quadratic: that controls the normalized all-pairs remainder; this must control bounded local templates hit by unequal coordinate conjugators.
  one-anchor-grading-makes-parity-damage-quadratic: that gives a quadratic formula for one common anchor grading; this concerns coordinate-dependent finite-Green gauges.
  averaged-pinching-channels-are-row-square-lipschitz: that transfers one averaged CP channel; this preserves sparse group-word residuals during iteration.
---

ESTABLISHED SPARSE-LEDGER REDUCTION.  For the damped intrinsic finite-Green
conjugators `(sigma k_i)` on the retained low-square block, every bounded
parity face and equality edge has damage controlled by the existing
balanced residual row square.  After local correction,

```text
 b_sparse,new<=C sigma^2 b_old+C epsilon_inv.           (SFR1)
```

The constant is independent of code length and dimension.  Consequently,
whenever the dense intrinsic step has a first-order gain
`b_dense,new<=(1-c sigma)b_old+O(sigma^2b_old)`, choose one fixed small
`sigma` and the sparse exactification cost is absorbed, giving a strict
combined contraction.

## Attempts

The intrinsic Green polynomial and covariant divergence have bounded cb
row/column norm, so the correction row satisfies

```text
 avg_i k_i^*k_i<=C_K b_old I                            (SFR2)
```

on the retained block, after adjoining the finite left/right symmetrization
of the raw square function.  Duhamel expansion of
`exp(sigma k_i)Q_i exp(-sigma k_i)` and fixed-width word telescoping show
that a face or equality residual created from an exact local tuple has
operator square bounded by `C sigma^2` times the corresponding finite
symmetrization of `(SFR2)`.  Bounded occurrence preserves this estimate
after averaging.

Apply `fixed-parity-faces-exactify-with-loewner-row-square-control` to every
face.  Its correction row square is Loewner-dominated by the newly created
sparse residual square, hence by `C sigma^2b_old I`.  The normalized
equality channel gap then transfers through
`normalized-occurrence-equality-transfer-preserves-face-gap`; the
equality-split low spectral band remains a vanishing energy floor by
`shared-pinching-low-band-is-gauge-or-cheap`.  Terminal block compression
and sign add only the involution forcing ledger.  This proves `(SFR1)`.

This closes the sparse-face/equality preservation gate.  The remaining
unproved input to `off-base-row-gradient-coercivity` is the first-order
dense low-sector curl/coercivity estimate; sparse local exactification no
longer obstructs it.
