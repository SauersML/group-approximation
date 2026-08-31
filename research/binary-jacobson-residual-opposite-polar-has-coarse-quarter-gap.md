---
rg: 2
id: binary-jacobson-residual-opposite-polar-has-coarse-quarter-gap
kind: claim
title: The last Jacobson opposite polar is full or pays a raw-cut quarter boundary
artifacts:
  - research/binary-jacobson-residual-opposite-polar-quarter-gap-proof.md
distinct_from:
  binary-jacobson-constant-opposite-polar-is-finite-s3: that compresses one constant opposite root on one negative constant-root cut and obtains a finite S3 polynomial; this combines the negative Q-head cut with the complementary ST joint sign cut and isolates the only further loss caused by the raw SQ/S2T carrier.
  binary-jacobson-native-v4-polar-orbit-leaves-one-residual: that locates the exact residual left by every typed source-row polar; this proves a dimension-independent support gap for the remaining opposite-root compression before the extra raw cuts are imposed.
  binary-jacobson-full-cycle-weyl-switches-residual-sign: that sends the residual to an orthogonal carrier by a unitary full-cycle word; this compresses the opposite root back to the same residual and gives a full-polar-or-boundary dichotomy.
---

**ESTABLISHED.** In

```text
J=F_2<S,T | TS=1>,       Q=1-ST,       P_0=ST,
```

put

```text
w=x_13(Q),       c=x_13(P_0),       r=x_23(P_0),
k_Q=x_31(Q),     k_P=x_31(P_0),     k=x_31(1)=k_Q k_P,
e_Q=(1-w)/2,     e_P=(1+c)(1-r)/4,  F=e_Qe_P.          (JRG1)
```

In every finite-dimensional unitary representation of this fixed root
packet, the self-adjoint compression

```text
A=FkF                                                        (JRG2)
```

is invertible on `F` and satisfies

```text
A^*A >= (1/16)F,              ||A^(-1)||_op <= 4.            (JRG3)
```

More generally, let `f<=F` be any projection and put

```text
B=fkf=fAf,                    L=(1-f)Af.                     (JRG4)
```

Then

```text
B^*B=fA^*Af-L^*L >= (1/16)f-L^*L.                           (JRG5)
```

Consequently the following exhaustive quantitative alternative holds:

```text
polar(fkf) has initial and final projection f,
or
||(1-f)Af||_op >= 1/4.                                     (JRG6)
```

The live residual projection `f=e_res` of
`binary-jacobson-native-v4-polar-orbit-leaves-one-residual` lies under `F`.
Indeed its defining signs include

```text
x_13(Q)=-1,       x_13(ST)=+1,
x_23(ST)=x_23(1)x_23(Q)=-1.                                (JRG7)
```

Thus the remaining constant opposite-root candidate cannot lose support for
an untyped coarse reason.  Either its polar is already a square unitary on
the entire raw residual, or the additional `SQ,S^2T` spectral cuts have a
fixed operator-norm boundary at least `1/4`.  The latter boundary is the
precise unresolved occurrence: this claim neither makes it a presentation
relator defect nor proves the four common PI covariance rows.

No trace, carrier-density estimate, Property `(T)`, or canonical character
is used.

DERIVATION
binary-jacobson-residual-opposite-polar-quarter-gap-proof
