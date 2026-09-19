---
rg: 2
id: sparse-face-row-square-proof
kind: route
title: Dampen the intrinsic gauges and re-exactify each fixed face in Loewner order
target: sparse-face-row-square-survives-intrinsic-green-step
requires:
  - fixed-parity-faces-exactify-with-loewner-row-square-control
  - intrinsic-finite-green-commutator-step-has-the-correct-tangent
  - normalized-occurrence-equality-transfer-preserves-face-gap
  - shared-pinching-low-band-is-gauge-or-cheap
  - common-cut-contraction-sign-has-complete-balanced-energy-ledger
---

Use the finite cb row bound of the intrinsic divergence and Green polynomial
to obtain `(SFR2)`.  Expand each damped coordinate conjugation by Duhamel.
Because every face and equality word has fixed length, its first variation
is `O(sigma)` in a fixed incidence sum of the `k_i`; operator Jensen and
bounded occurrence make the averaged residual square `O(sigma^2b_old)`.

Apply the fixed-face Loewner exactification to this new sparse residual.
Its correction square has the same order and the equality-channel transfer
has length-independent constants.  Leave the equality-created low spectral
band as the forcing floor supplied by the low-band theorem, and carry the
positive involution residual to terminal sign.  This proves `(SFR1)`.
