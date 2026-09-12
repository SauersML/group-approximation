---
rg: 2
id: binary-gl-finite-sections-have-no-projective-k2-phase
kind: claim
title: Binary general-linear finite sections have no projective phase that separates boundary from head
distinct_from:
  toeplitz-folner-compressions-cannot-retain-jacobson-head: that treats ordinary unitary representations after Toeplitz truncation; this computes the Schur class and rules out a genuine projective-multiplier repair
  torsion-symbols-exactify-by-corners-not-infinite-symbol: that constructs nontrivial Heisenberg clock-shift phases for an infinite central symbol; this proves the binary finite-section host has no corresponding central symbol
  binary-jacobson-steinberg-cover-is-elementary: that kills the Steinberg kernel over the Jacobson ring; this kills the finite-section Steinberg kernel over F_2 itself
---

For every `N>=1`, put `m=28N). Then

```text
H_2(GL_m(F_2),Z)=0,                                     (BGP1)
H^2(GL_m(F_2),U(1))=0.                                  (BGP2)
```

Consequently every finite-dimensional complex projective unitary
representation of `GL_m(F_2)` is projectively equivalent to an ordinary
unitary representation.

In particular the two rank-one transvections

```text
X_ik(P_(N-1)),                   X_ab(P_0)
```

from the Toeplitz finite-section calculation cannot acquire different
central lifts from a nontrivial Schur or stable-K-two class. After
linearization their images are unitarily conjugate exactly.

Thus a clock-shift multiplier does not repair the truncated-shift
construction. Any chosen projective lift differs from an ordinary
representation only by a scalar one-cochain on the finite group. If those
scalars are used to separate the one-sided-inverse defect from the head,
the construction has left the projective-multiplier mechanism: it is an
explicit nonfunctorial scalar perturbation whose compatibility with every
full-presentation relator must be proved separately.

This result does not yet rule out such relator-dependent one-cochain
perturbations, nor arbitrary perturbations of the root unitaries. It closes
the genuine Schur/K-two and clock-shift phase route exactly.

DERIVATION
stable-steinberg-cover-kills-clock-shift-multiplier-proof
