---
rg: 2
id: pauli-overlap-yields-positive-spectral-corner-proof
kind: route
title: Choose the heavier orientation and apply a fixed spectral threshold
target: pauli-overlap-yields-positive-spectral-corner
requires:
  - pauli-packet-incoming-mass-exceeds-corner-capacity
---

The two ordered terms sum to at least `5/32`, so one is at least `5/64`.
For a positive contraction of trace at least `5/64`, splitting its spectrum
below and above `5/128` gives
`5/64 <= (5/128)(1-p)+p`; hence `p>=5/123`.

