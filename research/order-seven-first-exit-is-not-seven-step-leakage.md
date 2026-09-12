---
rg: 2
id: order-seven-first-exit-is-not-seven-step-leakage
kind: claim
title: A low first-exit cut does not control the order-seven compression telescope
invalidates:
  - order-seven-compression-telescope-proof
  - fixed-finite-coordinate-cuts-force-order-seven-leakage-tail
  - order-seven-first-exit-closes-same-gram-certificate
artifacts:
  - research/order-seven-first-exit-counterexample-proof.md
distinct_from:
  native-whitehead-hecke-head-has-order-seven-anchor: that exact ordinary-word identity remains valid; this refutes only the passage from the one-step spectral quantity OSC3 to the seven-step compressed identity OSC2.
  finite-coordinate-el20-active-cut-inherits-order-seven-anchor: that requests all compression boundary terms on a positive common cut and calls OCI5 an equivalent load-bearing estimate; this proves that OCI5 is not equivalent to those boundary terms.
---

**ESTABLISHED ONE-STEP/ITERATED-BOUNDARY FENCE.**  Let `T` be a unitary
of order seven, let `Q` be a projection, and let `E<=Q`.  The estimate

```text
||(1-Q)TE||_2=o(1)                                     (OFE1)
```

does not control either `||(1-E)TE||_2` or any of the later exits
`||(1-Q)T^kE||_2`, `2<=k<=6`.  It therefore cannot be substituted into
the compression telescope

```text
||QT^7Q-(QTQ)^7||_2 <=6||(1-Q)TQ||_2.                 (OFE2)
```

In particular, the low spectral cut proposed after `(OSC3)--(OSC4)` in
`order-seven-anchor-stops-at-whitehead-compression-leakage` supplies only
`(OFE1)`.  The right side of `(OFE2)` contains the full source `Q`, not the
low spectral subcut `E`; applying the same telescope with `E` instead
requires `||(1-E)TE||_2`, which `(OFE1)` does not bound.

This failure already occurs with zero defect in dimension seven.  On the
standard basis `e_0,...,e_6`, let

```text
Te_j=e_(j+1 mod 7),       Q=e_0e_0^*+e_1e_1^*,
E=e_0e_0^*.                                             (OFE3)
```

Then `T^7=1` and `(1-Q)TE=0`, so the one-step leakage operator on `E` is
zero.  Nevertheless `ETE=0`, whence

```text
||(ETE)^7-E||_2=||E||_2>0,                             (OFE4)
```

and `T^2E` is orthogonal to `Q`.  Arbitrary amplification preserves zero
relation defect and the normalized relative gap.

Thus an order-seven repair must control an orbit-saturated boundary, for
example all operators

```text
(1-Q)T^kE,                  1<=k<=6,                  (OFE5)
```

or directly control `(1-E)TE`.  A first-exit spectral projection of
`Q T^*(1-Q)T Q` is not enough.  This is a finite-matrix obstruction and
uses no Property `(T)`, Kazhdan input, trace-profile assumption, or
literature theorem.

DERIVATION
order-seven-first-exit-counterexample-proof
