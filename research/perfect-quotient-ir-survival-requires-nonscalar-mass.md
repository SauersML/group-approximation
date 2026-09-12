---
rg: 2
id: perfect-quotient-ir-survival-requires-nonscalar-mass
kind: claim
title: IR survival for a finitely presented perfect quotient requires nonscalar retained mass
distinct_from:
  ir-survival-is-one-compressed-adjoint-moment: that identifies displacement from the identity as the exact scalar test for IR3 after IR1--IR2; this proves that, for a perfect quotient, the displacement cannot be carried only by scalar phase and must remain visible modulo all scalars.
  nonsofic-block-monomial-images-force-soft-kernel-labels: that detects soft labels in the kernel of the original block-monomial GNS model; this concerns the separately compressed IR representation and uses perfectness of its quotient.
  simple-map-quotient-has-rigid-fd-restriction: that rules out a nontrivial exact finite-dimensional quotient representation; this rules out asymptotically scalar retained representations in arbitrary growing dimension.
---

**ESTABLISHED NONSCALAR IR REQUIREMENT.** Let

```text
Q=<x_1,...,x_s | r_1,...,r_m>=F/K                     (PNS1)
```

be finitely presented and perfect.  Suppose `(IR1)--(IR2)` hold and let
`S_n(f) in U(r_n)` be the polar-corrected compressed maps constructed in
`leavitt-presentation-double-retention-proves-hyperlinear`.  If

```text
dist_(2,r_n)(S_n(x_j), T 1)->0            (1<=j<=s),   (PNS2)
```

where `T 1={lambda 1:|lambda|=1}`, then

```text
||S_n(f)-1||_(2,r_n)->0                   (f in F).    (PNS3)
```

Consequently `(IR3)` is impossible under `(PNS2)`.  Any successful IR model
for the binary Leavitt quotient must have, after a subsequence, some fixed
generator `x_j` and `eta>0` with

```text
inf_(|lambda|=1)||S_n(x_j)-lambda 1||_(2,r_n)>=eta.    (PNS4)
```

Equivalently, because `S_n(x_j)` is unitary,

```text
1-|tr_(r_n)(S_n(x_j))| >= eta^2/2.                     (PNS5)
```

Thus collapsing scalar phase labels are not by themselves the live Leavitt
escape.  The retained sector must carry a genuinely nonscalar adjoint
observable.  This does not rule out block-monomial IR: several phase or block
types can produce `(PNS4)`.  It only identifies the first necessary datum
which a scalar soft-label model lacks.

DERIVATION
perfect-presentation-kills-asymptotic-scalar-characters-proof
