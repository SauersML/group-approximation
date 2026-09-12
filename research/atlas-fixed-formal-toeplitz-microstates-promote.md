---
rg: 2
id: atlas-fixed-formal-toeplitz-microstates-promote
kind: claim
title: Fixed-width formal Toeplitz Atlas microstates promote to an exact finite-field point
distinct_from:
  atlas-block-circulant-joint-escape-promotes-to-exact-mode: that uses primary Fourier quotients of cyclic gauges; this treats lower-triangular finite sections of one formal power-series gauge, including singular cyclic symbols and global triangular inverses.
  atlas-low-rank-cyclic-perturbations-promote: that requires proximity to an invertible cyclic gauge; this does not use a cyclic closure at all.
  atlas-m2-kernel-phases-cannot-upper-toeplitz-stitch: that treats upper-triangular couplings of two calibrated finite phases; this treats an arbitrary fixed matrix power-series symbol and all augmented Laurent words simultaneously.
---

Fix a block size `b` and let

```text
B(z) in GL_b(F2[[z]])
```

have invertible constant coefficient.  For every `N`, let `T_N` be
multiplication by `B(z)` on

```text
(F2[z]/(z^N))^b.                                      (FTP1)
```

Then `T_N` is invertible, and its inverse is multiplication by the truncation
of the formal inverse `B(z)^-1`.  Evaluate the repeated-natural Atlas packet,
collision `19243`, and q14 using fixed block coefficient matrices and this
gauge.

If every augmented Laurent residual has rank `o(N)`, then

```text
R(B(z))=0 in Mat_b(F2[[z]])                            (FTP2)
```

for every augmented relation `R`.  Consequently the same finite algebraic
system has a point in `GL_b(F_(2^f))` for some finite extension of `F2`.
Restriction of scalars gives an exact finite binary Atlas zero and hence the
finite-quotient escape.

Therefore no fixed-width stationary companion/shift construction can realize
the wandering defect alternative, even when its cyclic closure is singular
and `T_N^-1` is a global triangular Toeplitz corrector.  A symbolic
counterexample to augmented rank compactness must have growing block/state
width or genuinely nonstationary coefficients; one fixed formal-series
symbol cannot do it.

