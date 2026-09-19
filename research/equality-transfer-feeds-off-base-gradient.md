---
rg: 2
id: equality-transfer-feeds-off-base-gradient
kind: route
title: Transfer the face gap through row-square equality and apply the intrinsic Green step
target: off-base-row-gradient-coercivity
requires:
  - parity-exact-shared-contractions-have-intrinsic-cp-gap
  - averaged-pinching-channels-are-row-square-lipschitz
  - row-square-equality-variance-transfers-averaged-pinching-gap
  - shared-pinching-low-band-is-gauge-or-cheap
  - sparse-face-row-square-survives-intrinsic-green-step
  - parity-charged-green-edge-curl-coercivity
  - parity-charge-or-green-divergence-has-strict-descent
  - intrinsic-finite-green-commutator-step-has-the-correct-tangent
---

Exact local faces supply a pre-character spectral gap for their averaged
coordinate channel.  Weighted equality variance and the averaged-channel
estimate transfer it to shared representatives, leaving only the small
spectral band created from the old commutant.  The low-band energy theorem
leaves that band as a vanishing forcing floor.  The intrinsic finite-Green step is a fixed
polynomial in the remaining channel, so the transferred gap gives strict
transverse contraction; the dense nonlinear remainder is cb-quadratic and
involution forcing is carried to terminal sign.  This yields `(ORG1)` once
the sparse face/equality theorem preserves the row-square hypothesis.

The sparse theorem is established by fixed-width Loewner exactification,
and `(PCG2)` charges the entire edge field to sparse/equality syndrome.
But this is not yet strict descent: the charge inequality has the wrong
direction to lower-bound the Green divergence, while Loewner
re-exactification bounds movement cost but does not contract the equality
charge.  The remaining input is exactly
`parity-charge-or-green-divergence-has-strict-descent`; equality transfer,
its low band, and bounded-cost sparse re-exactification are complete.
