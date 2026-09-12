---
rg: 2
id: bs14-even-weil-cross-cutoff-proof
kind: route
title: Use the even-Weil fixed line to force a short-long exact cell
target: bs14-native-cells-cross-every-length-cutoff
requires:
  - even-weil-fixed-line-compression
  - bs14-unitary-representations-are-periodic-cycle-packets
---

In the Schrödinger basis, the diagonal BS generator has one zero coordinate
and the nonzero coordinates are permuted by multiplication by four.  Every
nonzero orbit therefore has length `ord_p(4)` and return phase one.  If
these lengths were bounded by `M` for all primes `p=1 mod 4`, each such
prime would divide the integer `(NLC4)`, impossible.

The exact norm `(NLC5)` is computed in the proof of
`even-weil-fixed-line-compression`.  Since it is nonzero, the full Weil
involution crosses the decomposition `(NLC1)`.  The independent
nonextension argument in that claim shows the same fact without using the
matrix coefficient: block preservation would restrict every group
relation to `PH` and produce the forbidden same-dimensional extension.

