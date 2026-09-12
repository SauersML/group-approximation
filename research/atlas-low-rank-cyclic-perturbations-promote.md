---
rg: 2
id: atlas-low-rank-cyclic-perturbations-promote
kind: claim
title: Low-rank perturbations of fixed-block cyclic Atlas gauges still promote to exact modes
distinct_from:
  atlas-block-circulant-joint-escape-promotes-to-exact-mode: that assumes the gauges themselves are block-circulant; this allows arbitrary invertible gauges at vanishing normalized-rank distance from an invertible block-circulant sequence.
  atlas-m2-kernel-phases-cannot-upper-toeplitz-stitch: that reads exact diagonal phase defects through an invariant flag; this uses only Laurent-word rank Lipschitzness and cyclic mode promotion.
  sublinear-bandwidth-is-vacuous-under-rank-amplification: that shows a basis bandwidth condition does not restrict arbitrary rank microstates; this requires the much stronger basis-free condition of vanishing normalized-rank distance to one fixed-block cyclic gauge.
---

Fix a coefficient block size and the repeated-natural Atlas coefficient
matrices.  Let

```text
S_N = an invertible fixed-block circulant gauge,
T_N = any invertible gauge of the same size
```

over `F2`, and suppose

```text
rank(T_N-S_N)/N ->0.                                  (LCP1)
```

If every packet, collision `19243`, and q14 Laurent residual evaluated at
`T_N` has rank `o(N)`, then the same is true at `S_N`.  Consequently
`atlas-block-circulant-joint-escape-promotes-to-exact-mode` produces an
exact common zero over a finite extension of `F2`, and hence an exact binary
finite-quotient escape after restriction of scalars.

Thus, in the absence of an exact augmented finite escape, no gauge sequence
which is a vanishing-rank perturbation of a fixed-block invertible cyclic
sequence can realize a wandering Atlas defect seed.  In particular the
standard companion/finite-section construction—where closing the shift
changes only a bounded number of block rows—does not evade cyclic mode
promotion whenever its cyclic closure is invertible.

The qualifier is sharp.  This does not treat a width-growing block symbol,
a proposed cyclic closure which is singular, or a gauge with positive
normalized-rank distance from every fixed-block circulant.  Those are the
remaining possible symbolic wandering mechanisms.

