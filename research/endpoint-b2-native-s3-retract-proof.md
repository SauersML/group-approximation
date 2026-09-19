---
rg: 2
id: endpoint-b2-native-s3-retract-proof
kind: route
title: Quotient the column module by the zero-cylinder range ideal
target: endpoint-b2-enlargement-has-native-s3-retract
requires:
  - proper-support-returns-retain-constant-s3-retract
  - b2-pairs-full-hecke-first-support
---

Let `R` have characteristic two, let `p` be a proper idempotent, and suppose
invertible matrices `W_i` obey

```text
W_i-I in M_d(pR).                                      (1)
```

Every `W_i` preserves `(pR)^d`: the identity part preserves it, and a
matrix with entries in `pR` sends all of `R^d` into `(pR)^d`.  It induces
the identity on `(R/pR)^d`.

This quotient is nonzero.  Indeed `r=1-p` cannot lie in `pR`; if `r=px`,
then `pr=r`, while idempotence gives `pr=p(1-p)=0`, forcing `r=0`.

Constant elementary matrices preserve `(pR)^d`.  On two coordinates their
quotient images are the standard `F_2` transvections.  Since the quotient
is nonzero, those transformations generate a faithful `S_3`.  Thus quotient
action kills all `W_i` and is injective on the constant `S_3`.

Apply this with `p=s_0t_0`.  Every nonidentity coefficient of the three
Whiteheads in `(EBR1)` belongs to `pR`.  For `B_2`, the only deviation
coefficient is

```text
b_2=s_00t_1,                  p b_2=b_2.               (2)
```

The general quotient proves `(EBR2)`.  The MSI artifact checks this
coefficient by coefficient in faithful Leavitt normal form: the deviation
counts for `P,J_1,J_2,B_2` are `4,4,4,1`.  The second artifact performs the
independent depth-six word calibration.  Neither bounded computation is
needed for the all-word quotient argument.

