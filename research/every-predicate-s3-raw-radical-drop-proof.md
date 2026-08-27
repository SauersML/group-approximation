---
rg: 2
id: every-predicate-s3-raw-radical-drop-proof
kind: route
title: Symmetrically border the literal cycles and tensor their kernel with one hyperbolic plane
target: every-predicate-has-s3-equivariant-raw-radical-drop
requires:
  - boolean-violation-is-one-raw-radical-qubit-drop
  - phase-inverting-fourth-root-lifts-opposite-pauli-shears
---

If `C_f` is invertible, elementary block elimination shows the symmetric
matrix `S_f` in `(SER3)` is invertible.  Suppose instead that the block for
`a` is singular, with all-one left and right kernel vectors `u,v`.  A vector
`(s,t)` is in the kernel of `S_f` precisely when

```text
C_f t=0,                   C_f^T s+D t=0.                      (SER5)
```

Write `t=lambda v`.  Multiplying the second equation by `u^T` gives
`lambda u^T Dv=0`.  The chosen marked diagonal makes `u^TDv=1`, hence
`t=0`, and then `s` is a multiple of `u`.  Thus `S_f` has corank exactly
one and a fixed kernel word.  Tensor rank now proves `(SER1)` and identifies
the radical as `F_2^2 tensor <u>`.

Every matrix in `GL_2(F_2)` preserves `H`, so its tensor action preserves
every coefficient of `A_f`.  For the group lift, write the commutator entries
in the central basis `J,z_1,...,z_k` and adjoin roots
`R_i^2=z_i`.  A product of packet generators has one square defect in that
central basis; multiplying it by the corresponding product of `R_i` makes it
an involution.  Inverting the roots under either transvection cancels the
correction on the second application.  On each outer two-coordinate plane
the calculation is `(PIS2)--(PIS3)`, so the braid product has order three;
cross-plane commutators are preserved by the tensor isometry.

The artifacts verify every rank and raw kernel through all predicates of
arity three and audit the complete phase-root presentation for `(SER4)`.
