---
rg: 2
id: equal-rank-denominator-edges-authenticate-decoded-atoms
kind: claim
title: Equal-rank denominator edges transfer raw incidence directly to decoded atoms through first-exit mass
distinct_from:
  raw-denominator-incidence-kills-off-diagonal-shell-orbit: that compares raw balanced lamp conjugates and therefore encounters the trace-capacity obstruction when they are compared pointwise with a shell PVM; this compares two equal-rank decoded atoms through the actual section transition and never asks either atom to approximate a raw balanced lamp.
  polar-compression-turns-band-mismatch-into-first-exit: that constructs a partial isometry and controls its missing source and range from one compression; this adds the equal-rank projection identity which turns that same leakage into cross-chart atom authentication when the section correction stabilizes the source atom.
  partial-isometry-translate-cancel-charges-first-exit: that propagates an already supported triangle through missing sources and ranges; this is the preceding one-edge estimate that proves the two decoded source and range projections represent the same chart atom.
---

Let `(M,tau)` be a finite tracial von Neumann algebra.  Let `E,Ehat,F` be
projections with

```text
tau(E)=tau(Ehat)=tau(F),                                (EDA1)
```

and let `T,D` be unitaries.  Define

```text
ell=||(1-F)TE||_2^2,
eta=||DED^*-Ehat||_2,
epsilon=||T-D||_2.                                     (EDA2)
```

Then

```text
||TET^*-F||_2^2=2 ell,                                 (EDA3)
```

and consequently

```text
(1/2)||Ehat-F||_2^2
 <=2 ell+(eta+2 epsilon)^2
 <=2 ell+2 eta^2+8 epsilon^2.                          (EDA4)
```

The constants are independent of matrix dimension, projection rank,
congruence depth, and the number of conductor bands.

## Proof

Since `TET^*` and `F` have the same trace,

```text
||TET^*-F||_2^2
 =2 tau(E)-2 tau(FTET^*)
 =2||(1-F)TE||_2^2.                                    (EDA5)
```

Also

```text
||TET^*-DED^*||_2<=2||T-D||_2.                         (EDA6)
```

The triangle inequality gives

```text
||Ehat-F||_2<=eta+2epsilon+sqrt(2ell).                 (EDA7)
```

Applying `(a+b)^2/2<=a^2+b^2` with
`a=eta+2epsilon`, `b=sqrt(2ell)`, and then
`(eta+2epsilon)^2<=2eta^2+8epsilon^2`, proves `(EDA4)`.

## Arithmetic section interface

Use the fixed section identities

```text
a_i=b_i d_i,             d_i in C.                     (EDA8)
```

from `raw-denominator-incidence-kills-off-diagonal-shell-orbit`.  In a
matrix assignment put

```text
T_i=rho(b_i)^*rho(a_i),       D_i=rho(d_i).             (EDA9)
```

Fixed-area presentation telescoping gives

```text
epsilon_i=||T_i-D_i||_2<=C_sec delta.                  (EDA10)
```

Let `E_i,F_i` be equal-rank decoded atoms in the two charts, and let
`Ehat_i` be the root-chart atom prescribed by applying the label permutation
of `d_i` to `E_i`.  If

```text
ell_i=||(1-F_i)T_iE_i||_2^2                            (EDA11)
```

is entered in the first-exit ledger and

```text
eta_i=||D_iE_iD_i^*-Ehat_i||_2                         (EDA12)
```

is the decoded lattice covariance error, summing `(EDA4)`
gives

```text
Delta_w=(1/2)sum_i||Ehat_i-F_i||_2^2
 <=2 sum_i ell_i+2 sum_i eta_i^2
    +8 sum_i epsilon_i^2.                              (EDA13)
```

There are only `42` section words, so the last term is bounded by a fixed
constant times presentation defect squared.  Weyl symmetry supplies the
other four star links with the same finite maximum constant.

This bypasses the false pointwise target `(RDI10)`: no decoded atom is
compared with a trace-one-half raw lamp projection.  The raw arithmetic word
is used only as the transition `T_i`, and its failure to land in the target
decoded atom is literally first-exit mass.

The remaining hypothesis is structural rather than analytic: construct the
equal-rank decoded atoms so that `(EDA11)` belongs to the conductor
first-exit ledger and `(EDA12)` is controlled by the decoded full-coset PVM
covariance.  Once those objects exist, no additional support-authentication
or Hecke estimate is required to obtain the five cross-chart Gram
saturations.
