---
rg: 2
id: atlas-block-circulant-joint-escape-promotes-to-exact-mode
kind: claim
title: A block-circulant Atlas joint escape promotes to an exact finite-field mode
distinct_from:
  atlas-m2-kernel-phases-cannot-upper-toeplitz-stitch: that uses a flag-rank estimate for domain walls with finitely many wrap blocks; this treats genuinely circulant gauges by primary Fourier modes.
  atlas-exact-matrix-zero-set-is-a-finite-quotient-test: that starts from an exact matrix zero; this proves that a fixed-block circulant o-rank sequence necessarily produces such a zero.
  folner-multiplicity-atlases-have-vanishing-first-exit: that constructs coherent rectangular transport data without the Atlas kernel Laurent words; this uses those words mode by mode.
---

Fix a finite coefficient block and let `T_N` be an invertible block-circulant
effective H6 gauge over `F2[C_N]`.  Evaluate the full packet, collision
`19243`, and q14 using block-constant chart coefficients and seed frames.
If every residual has rank `o(N)` as `N` tends to infinity, then for every
sufficiently large member of the sequence there is a finite extension
`F_(2^f)/F2` and an invertible mode gauge `T(zeta)` over that extension which
satisfies **all** packet, collision, and q14 equations exactly.

Restriction of scalars therefore gives an exact finite-dimensional binary
joint model.  By the exact-matrix zero-set theorem, it gives a finite-quotient
escape for the augmented Atlas group.

Consequently block-circulant stitching is not a new approximate-only Følner
mechanism:

```text
o(N)-rank cyclic joint defects
        => exact finite-extension joint zero
        => exact finite-quotient escape.               (BCJ1)
```

In the absence of an exact finite quotient, every fixed-block circulant
sequence has a linear rank defect in at least one displayed relator.  The
statement allows arbitrary circulant bandwidth and also covers even cycle
lengths; characteristic-two Jordan modes do not evade `(BCJ1)`.
