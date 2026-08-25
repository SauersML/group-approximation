---
rg: 2
id: nonhyperlinear-from-binary-leavitt-native-cross-gram
kind: route
title: Use the native two-scale cross-Gram corner directly in canonical Steinberg microstates
target: non-hyperlinear-group
requires:
  - binary-leavitt-native-two-scale-cross-gram-positive
  - two-transport-cross-gram-has-a-fixed-mass-reducing-corner
  - two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge
  - two-shared-gauge-selector-rows-have-an-affine-rank-obstruction
---

Let

```text
Delta=St_20(L_2(F_2))
```

and use the fixed nonzero involutory root mark appearing in the native binary
packet.  If `Delta` were hyperlinear, canonical-trace microstates would send
that mark to asymptotic involutions with trace zero.  After finite-packet
exactification, its nontrivial spectral carrier therefore has normalized
trace `1/2+o(1)`.  In particular it is a positive-density active core of the
kind quantified over by
`binary-leavitt-native-two-scale-cross-gram-positive`; no operator-norm MF
radical or Property `(T)` input is needed.

The native cross-Gram estimate gives fixed positive Gram mass on that core.
By `two-transport-cross-gram-has-a-fixed-mass-reducing-corner`, cut to a
fixed-mass approximately reducing source corner and exactify the fixed packet
there.  The polar part of the two transports identifies their gauges on
corresponding positive subcorners.  The two mixed Pauli commutators then put
the relative polar unitary in the common multiplicity reservoir by
`two-mixed-pauli-commutators-lock-the-relative-reservoir-gauge`.

Thus the two scale-changing selector rows use one gauge on a corner whose
normalized mass stays bounded below.  But
`two-shared-gauge-selector-rows-have-an-affine-rank-obstruction` gives a fixed
positive lower bound for their total normalized-Hilbert--Schmidt row defect.
The defining group-word defects of a canonical microstate tend to zero, a
contradiction.  Hence `Delta` is nonhyperlinear.

This route is genuinely tracial.  It bypasses both
`binary-leavitt-two-shared-gauge-selector-compiler` and the operator-norm
property-`(T)`-free MF manuscript: the open native cross-Gram claim already
quantifies over positive-density HS microstate cores.
