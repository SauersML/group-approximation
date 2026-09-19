---
rg: 2
id: closed-a2-dyadic-generation-proof
kind: route
title: Generate every dyadic elementary root from one closed A2 reservoir and the denominator
target: closed-a2-dyadic-packet-saturates-the-sl3-actor
requires:
  - exact-projective-codensity-has-a-uniform-trace-square-gap
  - native-parahoric-triangle-kills-all-corrector-gauges
---

The four positive and negative simple-root generators give `SL_3(Z)`, hence
all signed Weyl permutations.  Repeated inverse conjugation of `x_12(1)` by
`h` gives `x_12(2^(-k))`; Weyl conjugation moves this element to every root
position, and powers supply every coefficient in `Z[1/2]`.  Elementary row
reduction over the Euclidean ring `Z[1/2]` proves that these elements generate
`SL_3(Z[1/2])`.

The two required claims then record the exact finite-dimensional co-density
and the dimension-free native-triangle collapse on an authenticated common
carrier.  Together they show both sides of the saturation boundary: exact
finite congruence models calibrate the full actor packet, while any already
common-supported corrector is coercively trivial.  What is not supplied is
the common-support extraction itself.

