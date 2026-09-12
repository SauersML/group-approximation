---
rg: 2
id: bs14-invariant-hull-weil-proof
kind: route
title: Use the full S-spectrum support of the deleted Fourier line
target: bs14-residual-invariant-hull-has-unbounded-packet-loss
requires:
  - even-weil-fixed-line-compression
  - deleted-fixed-line-first-cubic-has-explicit-positive-spectrum
---

The compressed cubic residual has rank at most two by
`deleted-fixed-line-first-cubic-has-explicit-positive-spectrum`, and its
unnormalized energy is bounded by four.  In the Schrödinger basis, `Xq` is
the normalized constant vector.  After removing its `q` coordinate, `PXq`
still has a nonzero coefficient on every nonzero even spectral line of
`S_0`.  Those eigenvalues are distinct on the primitive packet.  Therefore
the spectral projections of `S_0`, obtained by Lagrange interpolation, send
`PXq` onto every eigenline.  Its invariant hull has dimension `d`, proving
the claim.

